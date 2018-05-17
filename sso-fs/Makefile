# Makefile for sparse flow-sensitive alias analysis pass

# the default is a Debug build; uncomment one or more of the following to
# get the desired type of build
#
#DISABLE_ASSERTIONS=1
ENABLE_OPTIMIZED=1
#ENABLE_PROFILING=1

# for BuDDy and Google Perftools
USEDLIBS = bdd.a profiler.a

# Path to top level of LLVM heirarchy
LEVEL = ../../..

# Name of the library to build
LIBRARYNAME = SSaa

# Make the shared library become a loadable module so the tools can 
# dlopen/dlsym on the resulting library.
LOADABLE_MODULE = 1

# Include the makefile implementation stuff
include $(LEVEL)/Makefile.common
