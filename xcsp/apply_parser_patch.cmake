# Applies one patch to the fetched XCSP3-CPP-Parser, from FetchContent's
# PATCH_COMMAND. The patch step can run again on a tree it has already
# patched (a re-configure after the declaration changes, say), so this checks
# first and does nothing if the patch is already in place.
#
# Usage: cmake -DPATCH_FILE=<patch> -P apply_parser_patch.cmake, run in the
# parser's source directory.

find_package(Git REQUIRED)

execute_process(
    COMMAND ${GIT_EXECUTABLE} apply --reverse --check ${PATCH_FILE}
    RESULT_VARIABLE already_applied
    OUTPUT_QUIET ERROR_QUIET)
if(already_applied EQUAL 0)
    message(STATUS "XCSP3 parser patch already applied: ${PATCH_FILE}")
    return()
endif()

execute_process(
    COMMAND ${GIT_EXECUTABLE} apply ${PATCH_FILE}
    RESULT_VARIABLE result)
if(NOT result EQUAL 0)
    message(FATAL_ERROR "could not apply the XCSP3 parser patch ${PATCH_FILE}")
endif()
