# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.16

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /data/guangyuh/coding_env/supermini

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /data/guangyuh/coding_env/supermini/build

# Include any dependencies generated for this target.
include tip/CMakeFiles/tip-lib-static.dir/depend.make

# Include the progress variables for this target.
include tip/CMakeFiles/tip-lib-static.dir/progress.make

# Include the compile flags for this target's objects.
include tip/CMakeFiles/tip-lib-static.dir/flags.make

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.o: ../tip/tip/unroll/SimpBmc.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/unroll/SimpBmc.cc

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/unroll/SimpBmc.cc > CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/unroll/SimpBmc.cc -o CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.o: ../tip/tip/unroll/SimpBmc2.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/unroll/SimpBmc2.cc

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/unroll/SimpBmc2.cc > CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/unroll/SimpBmc2.cc -o CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.o: ../tip/tip/unroll/BasicBmc.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/unroll/BasicBmc.cc

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/unroll/BasicBmc.cc > CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/unroll/BasicBmc.cc -o CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.o: ../tip/tip/unroll/Unroll.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/unroll/Unroll.cc

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/unroll/Unroll.cc > CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/unroll/Unroll.cc -o CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.o: ../tip/tip/constraints/Embed.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/constraints/Embed.cc

tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/constraints/Embed.cc > CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/constraints/Embed.cc -o CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.o: ../tip/tip/constraints/Extract.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_6) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/constraints/Extract.cc

tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/constraints/Extract.cc > CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/constraints/Extract.cc -o CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.o: ../tip/tip/induction/RelativeInduction.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_7) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/induction/RelativeInduction.cc

tip/CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/induction/RelativeInduction.cc > CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/induction/RelativeInduction.cc -o CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.o: ../tip/tip/induction/TripProofInstances.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_8) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/induction/TripProofInstances.cc

tip/CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/induction/TripProofInstances.cc > CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/induction/TripProofInstances.cc -o CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.o: ../tip/tip/liveness/EmbedFairness.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_9) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/liveness/EmbedFairness.cc

tip/CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/liveness/EmbedFairness.cc > CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/liveness/EmbedFairness.cc -o CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.o: ../tip/tip/liveness/Liveness.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_10) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/liveness/Liveness.cc

tip/CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/liveness/Liveness.cc > CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/liveness/Liveness.cc -o CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.o: ../tip/tip/reductions/RemoveUnused.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_11) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/reductions/RemoveUnused.cc

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/reductions/RemoveUnused.cc > CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/reductions/RemoveUnused.cc -o CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.o: ../tip/tip/reductions/ExtractSafety.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_12) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/reductions/ExtractSafety.cc

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/reductions/ExtractSafety.cc > CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/reductions/ExtractSafety.cc -o CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.o: ../tip/tip/reductions/Substitute.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_13) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/reductions/Substitute.cc

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/reductions/Substitute.cc > CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/reductions/Substitute.cc -o CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.o: ../tip/tip/reductions/TemporalDecomposition.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_14) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/reductions/TemporalDecomposition.cc

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/reductions/TemporalDecomposition.cc > CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/reductions/TemporalDecomposition.cc -o CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.s

tip/CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.o: tip/CMakeFiles/tip-lib-static.dir/flags.make
tip/CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.o: ../tip/tip/TipCirc.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_15) "Building CXX object tip/CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.o"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.o -c /data/guangyuh/coding_env/supermini/tip/tip/TipCirc.cc

tip/CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.i"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /data/guangyuh/coding_env/supermini/tip/tip/TipCirc.cc > CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.i

tip/CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.s"
	cd /data/guangyuh/coding_env/supermini/build/tip && /bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /data/guangyuh/coding_env/supermini/tip/tip/TipCirc.cc -o CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.s

# Object files for target tip-lib-static
tip__lib__static_OBJECTS = \
"CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.o" \
"CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.o"

# External object files for target tip-lib-static
tip__lib__static_EXTERNAL_OBJECTS =

tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/unroll/SimpBmc2.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/unroll/BasicBmc.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/unroll/Unroll.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Embed.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/constraints/Extract.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/induction/RelativeInduction.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/induction/TripProofInstances.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/liveness/EmbedFairness.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/liveness/Liveness.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/reductions/RemoveUnused.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/reductions/ExtractSafety.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/reductions/Substitute.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/reductions/TemporalDecomposition.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/tip/TipCirc.cc.o
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/build.make
tip/libtip.a: tip/CMakeFiles/tip-lib-static.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/data/guangyuh/coding_env/supermini/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_16) "Linking CXX static library libtip.a"
	cd /data/guangyuh/coding_env/supermini/build/tip && $(CMAKE_COMMAND) -P CMakeFiles/tip-lib-static.dir/cmake_clean_target.cmake
	cd /data/guangyuh/coding_env/supermini/build/tip && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/tip-lib-static.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
tip/CMakeFiles/tip-lib-static.dir/build: tip/libtip.a

.PHONY : tip/CMakeFiles/tip-lib-static.dir/build

tip/CMakeFiles/tip-lib-static.dir/clean:
	cd /data/guangyuh/coding_env/supermini/build/tip && $(CMAKE_COMMAND) -P CMakeFiles/tip-lib-static.dir/cmake_clean.cmake
.PHONY : tip/CMakeFiles/tip-lib-static.dir/clean

tip/CMakeFiles/tip-lib-static.dir/depend:
	cd /data/guangyuh/coding_env/supermini/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /data/guangyuh/coding_env/supermini /data/guangyuh/coding_env/supermini/tip /data/guangyuh/coding_env/supermini/build /data/guangyuh/coding_env/supermini/build/tip /data/guangyuh/coding_env/supermini/build/tip/CMakeFiles/tip-lib-static.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : tip/CMakeFiles/tip-lib-static.dir/depend

