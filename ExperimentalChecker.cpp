
#include <stdlib.h>

#include "ClangSACheckers.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SymbolManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ConstraintManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.h"
#include "llvm/ADT/ImmutableMap.h"

//#define DEBUG

#define MAX_SIZE(x) (x).getMaxValue((x).getBitWidth())

using namespace clang;
using namespace ento;

enum taintState {
    Tainted,
    Dependent,
    OK
};

class taintPropagationData {
private:
    const MemRegion *value;
    bool isNull;
    taintState isTainted;
    llvm::APInt estimatedSize;
public:

    taintPropagationData(const MemRegion *v, taintState ts) {
        isNull = false;
        isTainted = ts;
        value = v;
        estimatedSize = MAX_SIZE(estimatedSize);
    }

    taintPropagationData(const MemRegion *v, bool n) {
        isNull = n;
        isTainted = OK;
        value = v;
        estimatedSize = MAX_SIZE(estimatedSize);
    }

    taintPropagationData(const MemRegion *v, bool n, taintState ts) {
        isNull = n;
        isTainted = ts;
        value = v;
        estimatedSize = MAX_SIZE(estimatedSize);
    }

    taintPropagationData(const MemRegion *v, const MemRegion *dep) {
        isNull = false;
        isTainted = Dependent;
        value = v;
        estimatedSize = MAX_SIZE(estimatedSize);
    }

    ~taintPropagationData() {
    }

    bool operator==(const MemRegion *v) {
#ifdef DEBUG
        llvm::outs() << "OP== - Start: " << value->getString() << " " << v->getString() << ".\n";
#endif
        if (value == v) {
#ifdef DEBUG
            llvm::outs() << "OP== - True - P: " << value->getString() << " - " << v->getString() << ".\n";
#endif
            return true;
        } else {
            if (value->getString().compare(v->getString()) == 0) {
#ifdef DEBUG
                llvm::outs() << "OP== - True - S: " << value->getString() << " - " << v->getString() << ".\n";
#endif    
                return true;
            }
        }
#ifdef DEBUG
        llvm::outs() << "OP== - False: " << value->getString() << " - " << v->getString() << ".\n";
#endif
        return false;
    }

    inline taintState getTaintState() {
        return isTainted;
    }

    inline void setTaintState(taintState ts) {
        isTainted = ts;
    }

    MemRegion const * getMemRegion() const {
        return value;
    }

    llvm::APInt getEstiamtedSize() {
        return estimatedSize;
    }

    void setEstiamtedSize(llvm::APInt s) {
        estimatedSize = s;
    }


};

class callStackEntry {
private:
    SVal value;
    StringRef caller;

public:

    callStackEntry(SVal v, StringRef s) {
        value = v;
        caller = s;
    }

    SVal getValue() const {
        return value;
    }

    StringRef getCallerName() const {
        return caller;
    }
};

namespace {

    class ExperimentalChecker : public Checker< check::PreCall,
    check::PostCall,
    check::Bind,
    check::PreStmt<CallExpr>,
    check::PostStmt<Expr>,
    check::Location,
    check::Event<ImplicitNullDerefEvent> > {
    private:
        mutable std::unique_ptr<BuiltinBug> BT_useTaintValueBug;
        mutable std::unique_ptr<BuiltinBug> BT_sizeMismatchBug;

        inline void initTaintBugType() const {
            if (!BT_useTaintValueBug)
                BT_useTaintValueBug.reset(new BuiltinBug(this, "Tainted value used as an argument", "Possibility of out-of-bounds access"));
        }

        inline void initSizeBugType() const {
            if (!BT_sizeMismatchBug)
                BT_sizeMismatchBug.reset(new BuiltinBug(this, "Size mismatch", "Possibility of out-of-bounds access"));
        }

    public:
        ExperimentalChecker();
        ~ExperimentalChecker();
        void checkPreCall(const CallEvent &Call, CheckerContext & C) const;
        void checkPostCall(const CallEvent &Call, CheckerContext & C) const;
        void checkBind(SVal Loc, SVal Val, const Stmt *S, CheckerContext & C) const;
        void checkPostStmt(const Expr *E, CheckerContext & C) const;
        void checkPreStmt(const CallExpr *CE, CheckerContext & C) const;
        void checkLocation(SVal Loc, bool IsLoad, const Stmt *S, CheckerContext & C) const;
        void checkEvent(ImplicitNullDerefEvent Event) const;
        taintState getTaintState(ProgramStateRef State, const MemRegion *MR) const;
        llvm::APInt getMREstimatedSize(ProgramStateRef State, const MemRegion *MR) const;
        bool isMRStored(ProgramStateRef State, const MemRegion *MR) const;
        bool changeMRDependingOn(ProgramStateRef State, const MemRegion * MR, const MemRegion * DR) const;
        template<class T>
        unsigned int getSetSize(T &Set) const;
    };
}

REGISTER_SET_WITH_PROGRAMSTATE(aditionalValueData, taintPropagationData *)
REGISTER_SET_WITH_PROGRAMSTATE(callStackData, callStackEntry *)

ExperimentalChecker::ExperimentalChecker() {

}

ExperimentalChecker::~ExperimentalChecker() {

}

void ExperimentalChecker::checkPreCall(const CallEvent &Call, CheckerContext &C) const {
    const Expr *CallE = Call.getOriginExpr();
    if (!CallE) {
        return;
    }
    const Decl * D = Call.getDecl();
    if (!D) {
        return;
    }
    const FunctionDecl *FD = D->getAsFunction();
    if (!FD || FD->getKind() != Decl::Function)
        return;
    C.addTransition(C.getState());
}

void ExperimentalChecker::checkPostCall(const CallEvent& Call, CheckerContext& C) const {
    ProgramStateRef state = C.getState();
    llvm::APInt tmpMaxIntVal;
    llvm::APInt sValDstSize;
    llvm::APInt sValSrcSize;
    llvm::APInt sValSize;
    tmpMaxIntVal = MAX_SIZE(tmpMaxIntVal);
    const Expr *CallE = Call.getOriginExpr();
    if (!CallE) {
        return;
    }
    int tmpTState;
    if (Call.getResultType()->isVoidType()) {
        const IdentifierInfo *FInfo = Call.getCalleeIdentifier();
        if (FInfo) {
#ifdef DEBUG
            llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call (void) " << FInfo->getNameStart() << " - " << Call.getArgSVal(0) << ".\n";
#endif
        }
    } else {
        const IdentifierInfo *FInfo = Call.getCalleeIdentifier();
        if (FInfo) {
            StringRef SR = FInfo->getName();
            int nArgs = Call.getNumArgs();
            if (nArgs == 1) {
                if (SR.compare("malloc") == 0) {
                    if (!Call.getArgSVal(0).isConstant()) {
                        tmpTState = getTaintState(state, Call.getArgSVal(0).getAsRegion());
                        callStackDataTy cStack = state->get<callStackData>();
                        unsigned int cStackSize = getSetSize(cStack);
                        if (cStackSize != 1) {
                            if (tmpTState == Tainted) {
                                taintPropagationData *tmpData = new taintPropagationData(C.getSVal(CallE).getAsRegion(), Call.getArgSVal(0).getAsRegion());
                                state = state->add<aditionalValueData>(tmpData);
#ifdef DEBUG
                                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call - TNT - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0) << ".\n";
#endif
                            } else {
                                if (tmpTState == Dependent) {
                                    taintPropagationData *tmpData = new taintPropagationData(C.getSVal(CallE).getAsRegion(), Call.getArgSVal(0).getAsRegion());
                                    state = state->add<aditionalValueData>(tmpData);
#ifdef DEBUG
                                    llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call - DEP - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0) << ".\n";
#endif
                                } else {
                                    taintPropagationData *tmpData = new taintPropagationData(C.getSVal(CallE).getAsRegion(), OK);
                                    state = state->add<aditionalValueData>(tmpData);
                                }
                            }

#ifdef DEBUG
                            llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call - !TNT - !DEP - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0) << ".\n";
#endif
                        } else {
                            callStackDataTy::iterator cStackIterator = cStack.begin();
                            const callStackEntry *dependency = *cStackIterator;
#ifdef DEBUG
                            llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Calll - DEP - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0) << ".\n";
#endif
                            if (dependency->getCallerName().compare("strlen") == 0) {

                                state = state->add<aditionalValueData>(new taintPropagationData(C.getSVal(CallE).getAsRegion(), dependency->getValue().getAsRegion()));
                            } else {
                                state = state->add<aditionalValueData>(new taintPropagationData(C.getSVal(CallE).getAsRegion(), Call.getArgSVal(0).getAsRegion()));
                            }
                            state = state->remove<callStackData>();
#ifdef DEBUG
                            llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call Stack- " << FInfo->getNameStart() << " - " << tmpTState << " - " << Call.getArgSVal(0) << " - Value - " << getSetSize(cStack) << ".\n";
#endif
                        }
                    } else {
#ifdef DEBUG
                        llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call - CC - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0) << ".\n";
#endif
                        SVal ArgZ = Call.getArgSVal(0);
                        switch (ArgZ.getSubKind()) {
                            case nonloc::ConcreteIntKind:
                            {
                                const nonloc::ConcreteInt& ConstArgInt = ArgZ.castAs<nonloc::ConcreteInt>();
                                taintPropagationData *tmpData = new taintPropagationData(C.getSVal(CallE).getAsRegion(), OK);
                                tmpData->setEstiamtedSize(ConstArgInt.getValue());
                                state = state->add<aditionalValueData>(tmpData);
#ifdef DEBUG
                                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - ConcreteIntKind - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0) << " - " << ConstArgInt.getValue() << ".\n";
#endif
                                break;
                            }
                            case nonloc::SymbolValKind:
#ifdef DEBUG
                                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - SymbolValKind -  TODO" << ".\n";
#endif                                
                                break;
                            case nonloc::LocAsIntegerKind:
#ifdef DEBUG
                                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - LocAsIntegerKind -  TODO" << ".\n";
#endif                                
                                break;
                            case nonloc::CompoundValKind:
#ifdef DEBUG
                                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - CompoundValKind -  TODO" << ".\n";
#endif
                                break;
                            case nonloc::LazyCompoundValKind:
#ifdef DEBUG
                                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - LazyCompoundValKind -  TODO" << ".\n";
#endif
                                break;
                            default:
                                break;
                        }
                    }

                }
                if (SR.compare("strlen") == 0) {
#ifdef DEBUG
                    llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call - AP - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0).getAsRegion() << ".\n";
#endif
                    state = state->add<callStackData>(new callStackEntry(C.getSVal(CallE), FInfo->getName()));
                }
            }
            if (nArgs == 2) {
                if (SR.compare("strcpy") == 0) {
                    taintState tmpTaintState = getTaintState(state, Call.getArgSVal(1).getAsRegion());
                    if (tmpTaintState == Tainted) {
                        if (!isMRStored(state, Call.getArgSVal(0).getAsRegion())) {
                            state = state->add<aditionalValueData>(new taintPropagationData(Call.getArgSVal(0).getAsRegion(), Tainted));
                        }
                        if (ExplodedNode * N = C.addTransition()) {
                            if (!BT_useTaintValueBug)
                                initTaintBugType();
                            BugReport *report = new BugReport(*BT_useTaintValueBug, BT_useTaintValueBug->getDescription(), N);
                            report->addRange(Call.getSourceRange());
                            C.emitReport(report);
                        }
                    }
                    if (tmpTaintState == OK) {
                        if (isMRStored(state, Call.getArgSVal(0).getAsRegion()) && isMRStored(state, Call.getArgSVal(1).getAsRegion())) {
                            llvm::APInt sValZeroSize = getMREstimatedSize(state, Call.getArgSVal(0).getAsRegion());
                            llvm::APInt sValOneSize = getMREstimatedSize(state, Call.getArgSVal(1).getAsRegion());
#ifdef DEBUG
                            llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - tmpTaint - AP - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0).getAsRegion() << " - " << sValZeroSize << ".\n";
#endif
                            if (sValOneSize.getZExtValue() > sValZeroSize.getZExtValue()) {
                                if (ExplodedNode * N = C.addTransition()) {
                                    if (!BT_sizeMismatchBug)
                                        initSizeBugType();
                                    BugReport *report = new BugReport(*BT_sizeMismatchBug, BT_sizeMismatchBug->getDescription(), N);
                                    report->addRange(Call.getSourceRange());
                                    C.emitReport(report);
                                }
                            }
                        }
                        if (isMRStored(state, Call.getArgSVal(0).getAsRegion())) {
                            //TODO: Update taint value
                        }
                        if (isMRStored(state, Call.getArgSVal(1).getAsRegion())) {

                        }
                    }
                }

#ifdef DEBUG
                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0) << ".\n";
#endif
            }
            if (nArgs == 3) {
                if (SR.compare("read") == 0) {
                    if (getTaintState(state, Call.getArgSVal(2).getAsRegion()) == Tainted) {
                        if (!isMRStored(state, Call.getArgSVal(1).getAsRegion())) {
                            state = state->add<aditionalValueData>(new taintPropagationData(Call.getArgSVal(1).getAsRegion(), Tainted));
                        }
                        if (ExplodedNode * N = C.addTransition()) {
                            if (!BT_useTaintValueBug)
                                initTaintBugType();
                            BugReport *report = new BugReport(*BT_useTaintValueBug, BT_useTaintValueBug->getDescription(), N);
                            report->addRange(Call.getSourceRange());
                            C.emitReport(report);
                        }
                    }

                }
                if (SR.compare("memcpy") == 0) {
                    taintState tmpTaintState = getTaintState(state, Call.getArgSVal(1).getAsRegion());
                    if (tmpTaintState == OK) {
#ifdef DEBUG
                        llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - tmpTaint - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0).getAsRegion() << " - " << tmpTaintState << ".\n";
#endif
                        if (isMRStored(state, Call.getArgSVal(0).getAsRegion()) && isMRStored(state, Call.getArgSVal(1).getAsRegion())) {
#ifdef DEBUG
                            llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - tmpTaint - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0).getAsRegion() << " - " << tmpTaintState << ".\n";
#endif
                            sValDstSize = getMREstimatedSize(state, Call.getArgSVal(0).getAsRegion());
                            sValSrcSize = getMREstimatedSize(state, Call.getArgSVal(1).getAsRegion());
                            if (Call.getArgSVal(2).isConstant()) {
                                const nonloc::ConcreteInt& ConstArgInt = Call.getArgSVal(2).castAs<nonloc::ConcreteInt>();
                                sValSize = ConstArgInt.getValue();
                            } else {
                                sValSize = getMREstimatedSize(state, Call.getArgSVal(2).getAsRegion());
                            }
                            //llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - tmpTaint - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(2) << ".\n";
                            if (sValSize.getZExtValue() > sValDstSize.getZExtValue()) {
                                if (ExplodedNode * N = C.addTransition()) {
                                    if (!BT_sizeMismatchBug)
                                        initSizeBugType();
                                    BugReport *report = new BugReport(*BT_sizeMismatchBug, BT_sizeMismatchBug->getDescription(), N);
                                    report->addRange(Call.getSourceRange());
                                    C.emitReport(report);
                                }
                            } else {
                                if (sValSize.getZExtValue() > sValSrcSize.getZExtValue()) {
                                    if (ExplodedNode * N = C.addTransition()) {
                                        if (!BT_sizeMismatchBug)
                                            initSizeBugType();
                                        BugReport *report = new BugReport(*BT_sizeMismatchBug, BT_sizeMismatchBug->getDescription(), N);
                                        report->addRange(Call.getSourceRange());
                                        C.emitReport(report);
                                    }
                                }
                            }
                        } else {
                            if (isMRStored(state, Call.getArgSVal(1).getAsRegion())) {
                                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - tmpTaint - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0).getAsRegion() << " - " << tmpTaintState << ".\n";
                            } else {
                                if (isMRStored(state, Call.getArgSVal(1).getAsRegion())) {
                                    llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - tmpTaint 1 - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0).getAsRegion() << " - " << tmpTaintState << ".\n";
                                } else {
                                    if (isMRStored(state, Call.getArgSVal(0).getAsRegion())) {
                                        llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - tmpTaint 0- " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0).getAsRegion() << " - " << tmpTaintState << ".\n";
                                    } else {
                                        llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - tmpTaint !0 !1- " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0).getAsRegion() << " - " << tmpTaintState << ".\n";
                                    }
                                }
                            }
                        }
                    }
                    if (tmpTaintState == Tainted) {
                        if (ExplodedNode * N = C.addTransition()) {
                            if (!BT_useTaintValueBug)
                                initSizeBugType();
                            BugReport *report = new BugReport(*BT_useTaintValueBug, BT_useTaintValueBug->getDescription(), N);
                            report->addRange(Call.getSourceRange());
                            C.emitReport(report);
                        }
                    }
                    if (!Call.getArgSVal(2).isConstant()) {
                        tmpTaintState = getTaintState(state, Call.getArgSVal(2).getAsRegion());
                        llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - tmpTaint - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(2) << " - " << tmpTaintState << ".\n";
                        if (tmpTaintState == Tainted) {
                            if (ExplodedNode * N = C.addTransition()) {
                                if (!BT_useTaintValueBug)
                                    initSizeBugType();
                                BugReport *report = new BugReport(*BT_useTaintValueBug, BT_useTaintValueBug->getDescription(), N);
                                report->addRange(Call.getSourceRange());
                                C.emitReport(report);
                            }
                        }
                    }
                }
            }
        }
        C.addTransition(state);
    }
}

void ExperimentalChecker::checkBind(SVal Loc, SVal Val, const Stmt* S, CheckerContext & C) const {
    if (!S) {
        return;
    }
    ProgramStateRef state = C.getState();
    const MemRegion *VMR = Val.getAsRegion();
    if (!VMR) {
        return;
    }
    QualType valTy;
    switch (S->getStmtClass()) {
        case Stmt::BinaryOperatorClass:
        {

            SymbolRef sRef = Val.getLocSymbolInBase();
            if (!sRef) {
                break;
            }
            valTy = sRef->getType();
            if (!valTy->isPointerType()) {
#ifdef DEBUG
                llvm::outs() << "Not pointer " << Val << ".\n";
#endif
                break;
            }
            const Type *TP = valTy.getTypePtr();
            if (!TP) {
                break;
            }
            QualType PointeeT = TP->getPointeeType();
            if (!PointeeT.isNull()) {
#ifdef DEBUG
                llvm::outs() << "NULL Pointer " << Val << ".\n";
#endif
                break;
            }
            break;
        }
        default:
        {
#ifdef DEBUG
            llvm::outs() << "Other operator: " << S->getStmtClassName() << Loc << "  to " << Val << ".\n";
#endif
            break;
        }
    }
    C.addTransition(state);
}

void ExperimentalChecker::checkPreStmt(const CallExpr* CE, CheckerContext & C) const {
    ProgramStateRef state = C.getState();
    const AnalysisDeclContext *ADC = C.getCurrentAnalysisDeclContext();
    if (!ADC) {
        return;
    }
    const Decl *D = ADC->getDecl();
    if (!D) {
        return;
    }
    const FunctionDecl *FD = D->getAsFunction();
    if (!FD) {
        return;
    }
    if (C.isCLibraryFunction(FD, "main")) {
        int nParams = FD->getNumParams();
        for (int i = 0; i < nParams; ++i) {
            SVal pSV = state->getLValue(FD->getParamDecl(i)->getCanonicalDecl(), C.getLocationContext());
            if (!isMRStored(state, pSV.getAsRegion())) {
                state = state->add<aditionalValueData>(new taintPropagationData(pSV.getAsRegion(), Tainted));
            }
        }
    }
    C.addTransition(state);
}

void ExperimentalChecker::checkPostStmt(const Expr *E, CheckerContext & C) const {
    ProgramStateRef state = C.getState();
    const LocationContext *Loc = C.getLocationContext();
    if (!Loc) {
        return;
    }
    SVal S = state->getSVal(E, Loc);
    const ElementRegion *ER = NULL;
    const VarRegion *VR = NULL;
    const FieldRegion *FR = NULL;
    const TypedValueRegion *TR = NULL;
    const SymbolicRegion *SR = NULL;
    QualType valTy;
#ifdef DEBUG
    llvm::outs() << C.getSourceManager().getSpellingLineNumber(E->getLocStart()) << " - Post STMT - Start: " << S << ".\n";
#endif
    if (getTaintState(state, S.getAsRegion()) == Tainted) {
        //  llvm::outs() << C.getSourceManager().getSpellingLineNumber(E->getLocStart()) << " - Tainted: " << S << ".\n";
    } else {
        // llvm::outs() << C.getSourceManager().getSpellingLineNumber(E->getLocStart()) << " - Not Tainted: " << S << ".\n";
    }
    //llvm::outs() << C.getSourceManager().getSpellingLineNumber(E->getLocStart()) << " - Post Expr STMT: " << S <<" - "<< S.getBaseKind() << ".\n";

    const MemRegion *MR = S.getAsRegion();
    if (!MR) {
        return;
    }
    switch (MR->getKind()) {
        case MemRegion::ElementRegionKind:
            //ER = MR->getAs<ElementRegion>();
            //llvm::outs() << C.getSourceManager().getSpellingLineNumber(E->getLocStart()) << " - Post STMT Element+TNT: " << ER->getSuperRegion()->getString() << " - " << S << " " << MR->getKind() << ".\n";
            //state = state->add<aditionalValueData>(new aditionalData(ER->getSuperRegion(), Tainted));
            break;
        case MemRegion::SymbolicRegionKind:
            //state = state->add<aditionalValueData>(new aditionalData(MR, Tainted));
            break;
        case MemRegion::FunctionTextRegionKind:
            //llvm::outs() << C.getSourceManager().getSpellingLineNumber(E->getLocStart()) << " - Post STMT FNC-TxT+TNT: " << MR->getString() << " - " << S << " " << MR->getKind() << ".\n";
            //state = state->add<aditionalValueData>(new aditionalData(MR, Tainted));
            break;
        case MemRegion::VarRegionKind:
            //VR = MR->getAs<VarRegion>();
            //llvm::outs() << C.getSourceManager().getSpellingLineNumber(E->getLocStart()) << " - Post STMT VarRegion+TNT: " << VR->getBaseRegion() << " - " << S << " " << MR->getKind() << ".\n";
            //state = state->add<aditionalValueData>(new aditionalData(MR, Tainted));
            break;
        case MemRegion::FieldRegionKind:
            //FR = MR->getAs<FieldRegion>();
            //llvm::outs() << C.getSourceManager().getSpellingLineNumber(E->getLocStart()) << " - Post STMT Field+TNT: " << FR->getBaseRegion() << " - " << FR->getSuperRegion() << " - " << FR->getDecl()->getNameAsString() << " - " << S << " " << C.getSymbolManager().getRegionValueSymbol(FR) << ".\n";
            //state = state->add<aditionalValueData>(new aditionalData(MR, Tainted));
            break;
        default:
            //llvm::outs() << C.getSourceManager().getSpellingLineNumber(E->getLocStart()) << " - Post STMT Other+TNT: " << MR->getString() << " - " << S << " " << MR->getKind() << ".\n";
            //state = state->add<aditionalValueData>(new aditionalData(MR, Tainted));
            break;
    }

    C.addTransition(state);
}

void ExperimentalChecker::checkLocation(SVal Loc, bool IsLoad, const Stmt* S, CheckerContext & C) const {
    ProgramStateRef state = C.getState();
    const MemRegion *MR = Loc.getAsRegion();
    if (!MR) {
        return;
    }
    switch (S->getStmtClass()) {
        case Stmt::ImplicitCastExprClass:
        {
            const ImplicitCastExpr *ICE = cast<ImplicitCastExpr>(S);
            if (!ICE) {
                break;
            }
            const Expr *Ex = ICE->getSubExpr();
            if (!Ex) {
                break;
            }
            const LocationContext *Loc = C.getLocationContext();
            if (!Loc) {
                break;
            }
            SVal SValue = state->getSVal(Ex, Loc);
            if (IsLoad) {
#ifdef DEBUG
                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(S->getLocStart()) << ")" << " - Load from <" << MR->getString() << "> value " << SValue << ".\n";
#endif
            } else {
#ifdef DEBUG
                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(S->getLocStart()) << ")" << " - Store to <" << MR->getString() << "> value " << SValue << ".\n";
#endif
            }
            break;
        }
        case Stmt::DeclRefExprClass:
        {
            const DeclRefExpr *DRE = cast<DeclRefExpr>(S);
            if (!DRE) {
                break;
            }
            const Decl *DL = DRE->getDecl();
            if (!DL) {
                break;
            }
            if (DL->getKind() == Decl::Var) {
                if (IsLoad) {
#ifdef DEBUG
                    llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(S->getLocStart()) << ")" << " - Load DCL from <" << MR->getString() << "> value " << DL->getDeclKindName() << ".\n";
#endif
                } else {
#ifdef DEBUG
                    llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(S->getLocStart()) << ")" << " - Store DCL to <" << MR->getString() << "> value " << DL->getDeclKindName() << ".\n";
#endif
                }
            }
            break;
        }
        case Stmt::MemberExprClass:
        {
            const MemberExpr *ME = cast<MemberExpr>(S);
            if (!ME) {
                break;
            }
            const ValueDecl *VD = ME->getMemberDecl();
            if (!VD) {
                break;
            }
            if (IsLoad) {
#ifdef DEBUG
                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(S->getLocStart()) << ")" << " - Load MC from <" << MR->getString() << "> value " << VD->getNameAsString() << ".\n";
#endif
            } else {
#ifdef DEBUG
                llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(S->getLocStart()) << ")" << " - Store MC to <" << MR->getString() << "> value " << VD->getNameAsString() << ".\n";
#endif
            }
            break;
        }
        default:
#ifdef DEBUG
            llvm::outs() << "Other location: " << Loc << ".\n";
#endif
            break;
    }
    C.addTransition(state);
}

void ExperimentalChecker::checkEvent(ImplicitNullDerefEvent Event) const {
#ifdef DEBUG
    llvm::outs() << "Event: " << Event.Location << ".\n";
#endif
}

taintState ExperimentalChecker::getTaintState(ProgramStateRef State, const MemRegion * MR) const {
    if (!MR) {
        return OK;
    }
    const SymbolicRegion *compareSubRegion = NULL;
    aditionalValueDataTy ASet = State->get<aditionalValueData>();
    aditionalValueDataTy::iterator sEnd = ASet.end();
    aditionalValueDataTy::iterator I = ASet.begin();
    if (ASet.isEmpty()) {
        return OK;
    }
#ifdef DEBUG
    llvm::outs() << "GTS - Start: " << " - " << MR->getString() << ".\n";
#endif
    for (; I != sEnd; ++I) {
#ifdef DEBUG
        llvm::outs() << "CMP: (" << (*I)->getMemRegion() << ") - (" << MR << ").\n";
#endif
        if (((taintPropagationData) **I) == MR) {
#ifdef DEBUG
            llvm::outs() << "Found: " << MR->getString() << ".\n";
#endif
            break;
        } else {
            compareSubRegion = MR->getSymbolicBase();
            if (!compareSubRegion) {
#ifdef DEBUG
                llvm::outs() << "GTS - SB - Null: " << MR->getString() << ".\n";
#endif
                continue;
            }
#ifdef DEBUG
            llvm::outs() << "GTS  - BaseRegion: " << MR->getString() << " " << (*I)->getMemRegion()->getString() << " " << compareSubRegion->getString() << ".\n";
#endif
            if (((taintPropagationData) **I) == compareSubRegion->getBaseRegion()) break;
        }
#ifdef DEBUG
        llvm::outs() << "Not found: " << MR->getString() << " " << *I << " " << MR << ".\n";
#endif
    }
    if (I == sEnd) {
#ifdef DEBUG
        llvm::outs() << "GTS - Not found: " << " - " << MR->getString() << ".\n";
#endif
        return OK;
    } else {
#ifdef DEBUG
        llvm::outs() << "GTS - Found: " << " - " << MR->getString() << ".\n";
#endif
        return ((taintPropagationData)**I).getTaintState();
    }
}

llvm::APInt ExperimentalChecker::getMREstimatedSize(ProgramStateRef State, const MemRegion * MR) const {
    llvm::APInt maxValue;
    maxValue = MAX_SIZE(maxValue);
    if (!MR) {
        return maxValue;
    }
    const SymbolicRegion *compareSubRegion = NULL;
    aditionalValueDataTy ASet = State->get<aditionalValueData>();
    aditionalValueDataTy::iterator sEnd = ASet.end();
    aditionalValueDataTy::iterator I = ASet.begin();
    if (ASet.isEmpty()) {
        return maxValue;
    }
#ifdef DEBUG
    llvm::outs() << "GMRE - Start: " << " - " << MR->getString() << ".\n";
#endif
    for (; I != sEnd; ++I) {
#ifdef DEBUG
        llvm::outs() << "CMP: (" << (*I)->getMemRegion() << ") - (" << MR << ").\n";
#endif
        if (((taintPropagationData) **I) == MR) {
#ifdef DEBUG
            llvm::outs() << "Found: " << MR->getString() << ".\n";
#endif
            break;
        } else {
            compareSubRegion = MR->getSymbolicBase();
            if (!compareSubRegion) continue;
            if (((taintPropagationData) **I) == compareSubRegion->getBaseRegion()) break;
        }
#ifdef DEBUG
        llvm::outs() << "Not found: " << MR->getString() << " " << *I << " " << MR << ".\n";
#endif
    }
    if (I == sEnd) {
#ifdef DEBUG
        llvm::outs() << "GMRE - Not found: " << " - " << MR->getString() << ".\n";
#endif
        return maxValue;
    } else {
#ifdef DEBUG
        llvm::outs() << "GMRE - Found: " << " - " << MR->getString() << ".\n";
#endif
        return ((taintPropagationData)**I).getEstiamtedSize();
    }
}

bool ExperimentalChecker::isMRStored(ProgramStateRef State, const MemRegion * MR) const {
    if (!MR) {
        return false;
    }
    const SymbolicRegion *compareSubRegion = NULL;
    aditionalValueDataTy ASet = State->get<aditionalValueData>();
    aditionalValueDataTy::iterator sEnd = ASet.end();
    aditionalValueDataTy::iterator I = ASet.begin();
    if (ASet.isEmpty()) {
        return false;
    }
#ifdef DEBUG
    llvm::outs() << "MRStr - Start: " << " - " << MR->getString() << ".\n";
#endif
    for (; I != sEnd; ++I) {
        if (((taintPropagationData) **I) == MR) {
            break;
        } else {
            compareSubRegion = MR->getSymbolicBase();
            if (!compareSubRegion) continue;

            if (((taintPropagationData) **I) == compareSubRegion->getBaseRegion()) break;
        }

    }
    if (I == sEnd) {
#ifdef DEBUG
        llvm::outs() << "MRStr - Not found: " << " - " << MR->getString() << ".\n";
#endif
        return false;
    } else {
#ifdef DEBUG
        llvm::outs() << "MRStr - Found: " << " - " << MR->getString() << ".\n";
#endif
        return true;
    }
}

template<class T>
unsigned int ExperimentalChecker::getSetSize(T & Set) const {
    if (Set.isEmpty()) {
        return 0;
    }
    typename T::iterator sEnd = Set.end();
    typename T::iterator I = Set.begin();
    int i = 0;
    for (; I != sEnd; ++I, ++i) {
    }
    return i;
}

void ento::registerExperimentalChecker(CheckerManager & mgr) {
    mgr.registerChecker<ExperimentalChecker>();
}
