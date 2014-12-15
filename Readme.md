# Experimental Checker

## Getting Started
* Tested with LLVM 3.5.0
1. Checkout LLVM:
	$ svn co http://llvm.org/svn/llvm-project/llvm/trunk llvm
2. Checkout Clang:
		'''
		$ cd llvm/tools
		$ svn co http://llvm.org/svn/llvm-project/cfe/trunk clang
		$ cd ../..
		'''
3. Checkout extra Clang Tools:
	$ cd llvm/tools/clang/tools
	$ svn co http://llvm.org/svn/llvm-project/clang-tools-extra/trunk extra
	$ cd ../../../..
4. Checkout Compiler-RT:
	$ cd llvm/projects
	$ svn co http://llvm.org/svn/llvm-project/compiler-rt/trunk compiler-rt
	$ cd ../..
5. Get ExperimentalChecker:
	$ cd llvm/tools/clang/lib/StaticAnalyzer/Checkers/
	$ git clone git@github.com:danielovs/ExperimentalChecker.git .
	$ cd ../../../../..
	* _CMakeLists.txt_ and _Checkers.td_ will be modified
6. Build LLVM and Clang:
	$ ./configure
	$ make
7. (optional) Add scan-build to PATH variable:
	$ PATH=$PATH:`pwd`/tools/clang/tools/scan-build/

## Usage
1. Compile sources using checker:
	$ scan-build -enable-checker alpha.security.ExperimentalChecker --use-analyzer $CLANG_PATH make
	* Where `$CLANG_PATH` points to _clang_ binary
2. Results will be stored to _/tmp_ as _scan_build-*_

## How it works

* TODO
