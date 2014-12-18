# Experimental Checker

## Getting Started
1. Checkout LLVM:
```sh
		$ svn co http://llvm.org/svn/llvm-project/llvm/trunk llvm
```
2. Checkout Clang:
```sh
		$ cd llvm/tools
		$ svn co http://llvm.org/svn/llvm-project/cfe/trunk clang
		$ cd ../..
```
3. Checkout extra Clang Tools:
```sh
		$ cd llvm/tools/clang/tools
		$ svn co http://llvm.org/svn/llvm-project/clang-tools-extra/trunk extra
		$ cd ../../../..
```
4. Checkout Compiler-RT:
```sh
		$ cd llvm/projects
		$ svn co http://llvm.org/svn/llvm-project/compiler-rt/trunk compiler-rt
		$ cd ../..
```
5. Get ExperimentalChecker:
```sh
		$ cd llvm/tools/clang/lib/StaticAnalyzer/Checkers/
		$ git clone git@github.com:danielovs/ExperimentalChecker.git .
		$ cd ../../../../..
```
	* _CMakeLists.txt_ and _Checkers.td_ will be modified
6. Build LLVM and Clang:
```sh
		$ ./configure
		$ make
```
7. (optional) Add scan-build to PATH variable:
```sh
		$ PATH=$PATH:`pwd`/tools/clang/tools/scan-build/
```
## Usage
1. Compile sources using checker:
```sh
		$ scan-build -enable-checker alpha.security.ExperimentalChecker --use-analyzer $CLANG_PATH make
```
	* Where $CLANG_PATH points to clang binary
2. Results will be stored to _/tmp_ as _scan_build-*_

## How it works

The goal of first part of this project is to provide easy to use API to propagate taint state among different states of static analysis. It's possible to taint every single Memory Region. Taint state can be also enhanced by additional data like estimated size of Memory Region or dependency to another value/variable which can help in further analysis, for example to reduce the number of false positives. This data are always synchronized with analysis state so even if backtracking steps are done taint data correspond with this new state.

The second part of this project aims to use this data to check selected program states for possible bugs. There are three different types of generated warnings so far. They are described as follows:

* _Tainted value used as an argument_ – This warning is generated if one of selected operation uses tainted value as an argument. Generated warning is based only on taint state but there are implemented some improvements to reduce number of false positives using dependency data. Functions like strcpy, memcpy end their modifications should be scanned in this case. 

* _Size mismatch_ – This part of the checker uses advanced data to find if there is no possibility of boundary overflow. The enhanced size of Memory Regions is used to check this characteristic. The enhanced size of checked elements can be also updated during this tests.

* _Reading from tainted source_ – Incomplete part of checker which aims to check reading from the opened socket. File descriptor of opened socket is always considered as untrusted in this case. It provides only a lot of false positives now but it is under development.

* TODO
