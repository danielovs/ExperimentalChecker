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
public:

    taintPropagationData(const MemRegion *v, taintState ts) {
        isNull = false;
        isTainted = ts;
        value = v;
    }

    taintPropagationData(const MemRegion *v, bool n) {
        isNull = n;
        isTainted = OK;
        value = v;
    }

    taintPropagationData(const MemRegion *v, bool n, taintState ts) {
        isNull = n;
        isTainted = ts;
        value = v;
    }

    taintPropagationData(const MemRegion *v, const MemRegion *dep) {
        isNull = false;
        isTainted = Dependent;
        value = v;
    }

    ~taintPropagationData() {
    }

    bool operator==(const MemRegion *v) {
        return value == v;
    }

    inline taintState getTaintState() {
        return isTainted;
    }

    MemRegion const * getMemRegion() const {
        return value;
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

    SVal getValue() {
        return value;
    }

    StringRef getCallerName() {
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

        inline void initBugType() const {
            if (!BT_useTaintValueBug)
                BT_useTaintValueBug.reset(new BuiltinBug(this, "Tainted value used as an argument", "Possibility of out-of-bounds access"));
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
        bool isMRStored(ProgramStateRef State, const MemRegion *MR) const;
        bool changeMRDependingOn(ProgramStateRef State, const MemRegion * MR, const MemRegion * DR) const;
        template<class T>
        unsigned int getSetSize(T &Set) const;
    };
}

REGISTER_SET_WITH_PROGRAMSTATE(aditionalValueData, taintPropagationData *)
REGISTER_LIST_WITH_PROGRAMSTATE(callStackData, callStackEntry *)

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
    const FunctionDecl *FD = D->getAsFunction();
    if (!FD || FD->getKind() != Decl::Function)
        return;
    C.addTransition(C.getState());
}

void ExperimentalChecker::checkPostCall(const CallEvent& Call, CheckerContext& C) const {
    ProgramStateRef state = C.getState();
    const Expr *CallE = Call.getOriginExpr();
    int tmpTState;
    if (!CallE) {
        return;
    }
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
                        //#ifdef DEBUG
                        callStackDataTy cStack = state->get<callStackData>();
                        llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call - " << FInfo->getNameStart() << " - " << tmpTState << " - " << Call.getArgSVal(0) << " - Size - " << getSetSize(cStack) << ".\n";
                        //#endif
                        if (tmpTState == Tainted) {
                            state = state->add<aditionalValueData>(new taintPropagationData(C.getSVal(CallE).getAsRegion(), Call.getArgSVal(0).getAsRegion()));
                            //#ifdef DEBUG
                            llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call - TNT - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0) << ".\n";
                            //#endif
                        }
                        if (tmpTState == Dependent) {
                            state = state->add<aditionalValueData>(new taintPropagationData(C.getSVal(CallE).getAsRegion(), Call.getArgSVal(0).getAsRegion()));
                            //#ifdef DEBUG
                            llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call - DEP- " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0) << ".\n";
                            //#endif
                        }
                    }
                }
                if (SR.compare("strlen") == 0) {
                    llvm::outs() << "(" << C.getSourceManager().getSpellingLineNumber(CallE->getLocStart()) << ") - Post Call - AP - " << FInfo->getNameStart() << " - returns " << C.getSVal(CallE) << " - " << Call.getArgSVal(0).getAsRegion() << ".\n";
                    state = state->add<callStackData>(new callStackEntry(C.getSVal(CallE), FInfo->getName()));
                }
            }
            if (nArgs == 2) {
                if (SR.compare("strcpy") == 0) {
                    if (getTaintState(state, Call.getArgSVal(1).getAsRegion()) == Tainted) {
                        if (!isMRStored(state, Call.getArgSVal(0).getAsRegion())) {
                            state = state->add<aditionalValueData>(new taintPropagationData(Call.getArgSVal(0).getAsRegion(), Tainted));
                        }
                        if (ExplodedNode * N = C.addTransition()) {
                            if (!BT_useTaintValueBug)
                                initBugType();
                            BugReport *report = new BugReport(*BT_useTaintValueBug, BT_useTaintValueBug->getDescription(), N);
                            report->addRange(Call.getSourceRange());
                            C.emitReport(report);
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
                                initBugType();
                            BugReport *report = new BugReport(*BT_useTaintValueBug, BT_useTaintValueBug->getDescription(), N);
                            report->addRange(Call.getSourceRange());
                            C.emitReport(report);
                        }
                    }

                }
            }
        }
        C.addTransition(state);
    }
}

void ExperimentalChecker::checkBind(SVal Loc, SVal Val, const Stmt* S, CheckerContext & C) const {
    ProgramStateRef state = C.getState();
    const MemRegion *VMR = Val.getAsRegion();
    QualType valTy;
    switch (S->getStmtClass()) {
        case Stmt::BinaryOperatorClass:
        {
            if (VMR) {
                SymbolRef sRef = Val.getLocSymbolInBase();
                valTy = sRef->getType();
                if (!valTy->isPointerType()) {
#ifdef DEBUG
                    llvm::outs() << "Not pointer " << Val << ".\n";
#endif
                    break;
                }
                const Type *TP = valTy.getTypePtr();
                QualType PointeeT = TP->getPointeeType();
                if (!PointeeT.isNull()) {
#ifdef DEBUG
                    llvm::outs() << "NULL Pointer " << Val << ".\n";
#endif
                }
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
    const Decl *D = ADC->getDecl();
    const FunctionDecl *FD = D->getAsFunction();
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
    SVal S = state->getSVal(E, Loc);
    const ElementRegion *ER = NULL;
    const VarRegion *VR = NULL;
    const FieldRegion *FR = NULL;
    const TypedValueRegion *TR = NULL;
    const SymbolicRegion *SR = NULL;
    QualType valTy;
    if (getTaintState(state, S.getAsRegion()) == Tainted) {
        //llvm::outs() << C.getSourceManager().getSpellingLineNumber(E->getLocStart()) << " - Tainted: " << S << ".\n";
    } else {
        //llvm::outs() << C.getSourceManager().getSpellingLineNumber(E->getLocStart()) << " - Not Tainted: " << S << ".\n";
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
    switch (S->getStmtClass()) {
        case Stmt::ImplicitCastExprClass:
        {
            const ImplicitCastExpr *ICE = cast<ImplicitCastExpr>(S);
            const Expr *Ex = ICE->getSubExpr();
            const LocationContext *Loc = C.getLocationContext();
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
            const Decl *DL = DRE->getDecl();
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
            const ValueDecl *VD = ME->getMemberDecl();
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
            if (compareSubRegion->getBaseRegion() == MR) break;
            if (compareSubRegion->getSuperRegion() == MR) break;
        }
#ifdef DEBUG
        llvm::outs() << "Not found: " << MR->getString() << " " << *I << " " << MR << ".\n";
#endif
    }
    if (I == sEnd) {
        return OK;
    } else {
        return ((taintPropagationData)**I).getTaintState();
    }
}

bool ExperimentalChecker::isMRStored(ProgramStateRef State, const MemRegion * MR) const {
    if (!MR) {
        return false;
    }
    aditionalValueDataTy ASet = State->get<aditionalValueData>();
    aditionalValueDataTy::iterator sEnd = ASet.end();
    aditionalValueDataTy::iterator I = ASet.begin();
    if (ASet.isEmpty()) {
        return false;
    }
    for (; I != sEnd; ++I) {
        if (((taintPropagationData) **I) == MR) {
            break;
        }
    }
    if (I == sEnd) {
        return false;
    } else {
        return true;
    }
}

template<class T>
unsigned int ExperimentalChecker::getSetSize(T &Set) const {
    if (Set.isEmpty()) {
        return 0;
    }
    typename T::iterator sEnd = Set.end();
    typename T::iterator I = Set.begin();
    int i = 0;
    for (; I != sEnd; ++I, ++i) { }
    return i;
}

void ento::registerExperimentalChecker(CheckerManager & mgr) {
    mgr.registerChecker<ExperimentalChecker>();
}
