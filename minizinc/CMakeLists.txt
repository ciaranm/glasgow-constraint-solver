add_executable(fzn-glasgow fzn_glasgow.cc)
target_link_libraries(fzn-glasgow PRIVATE glasgow_constraint_solver cxxopts gcs_fmt nlohmann_json::nlohmann_json)

# The solver configuration is generated, twice, from glasgow.msc.in (issue #977).
# MiniZinc resolves a relative "executable" against the .msc's own directory, but
# when nothing is there it falls back silently to the working directory and then
# PATH, so a hand-written relative path runs whichever fzn-glasgow the cwd happens
# to reach. Hence:
#
# - The build tree gets <dir of fzn-glasgow>/glasgow.msc, with absolute paths: the
#   binary this build made, and the source tree's mznlib, so that editing a .mzn
#   there takes effect without rebuilding. It is per configuration, since
#   multi-config generators put each configuration's binary somewhere different.
#   ctest uses this file too, so it is the one that gets exercised.
# - The install gets <datadir>/minizinc/solvers/glasgow.msc, with paths relative to
#   itself, the same layout as the solvers in MiniZinc's own bundle, which keeps
#   the install relocatable (`cmake --install --prefix` picks the prefix after
#   configure time). A relative path is only right if it does not depend on the
#   prefix, so a BINDIR or DATADIR configured as absolute gets absolute paths.
set(GCS_MSC_EXECUTABLE "$<TARGET_FILE:fzn-glasgow>")
set(GCS_MSC_MZNLIB "${CMAKE_CURRENT_SOURCE_DIR}/mznlib")
configure_file(glasgow.msc.in ${CMAKE_CURRENT_BINARY_DIR}/glasgow.msc.build-tree @ONLY)
file(GENERATE OUTPUT $<TARGET_FILE_DIR:fzn-glasgow>/glasgow.msc
     INPUT ${CMAKE_CURRENT_BINARY_DIR}/glasgow.msc.build-tree)

set(_gcs_msc_install_dir ${CMAKE_INSTALL_DATADIR}/minizinc/solvers)
set(_gcs_mznlib_install_dir ${CMAKE_INSTALL_DATADIR}/minizinc/glasgow)
set(_gcs_fzn_install_file ${CMAKE_INSTALL_BINDIR}/fzn-glasgow${CMAKE_EXECUTABLE_SUFFIX})
if(IS_ABSOLUTE ${CMAKE_INSTALL_BINDIR} OR IS_ABSOLUTE ${CMAKE_INSTALL_DATADIR})
    set(GCS_MSC_EXECUTABLE ${CMAKE_INSTALL_FULL_BINDIR}/fzn-glasgow${CMAKE_EXECUTABLE_SUFFIX})
    set(GCS_MSC_MZNLIB ${CMAKE_INSTALL_FULL_DATADIR}/minizinc/glasgow)
else()
    file(RELATIVE_PATH GCS_MSC_EXECUTABLE ${CMAKE_INSTALL_PREFIX}/${_gcs_msc_install_dir} ${CMAKE_INSTALL_PREFIX}/${_gcs_fzn_install_file})
    file(RELATIVE_PATH GCS_MSC_MZNLIB ${CMAKE_INSTALL_PREFIX}/${_gcs_msc_install_dir} ${CMAKE_INSTALL_PREFIX}/${_gcs_mznlib_install_dir})
endif()
configure_file(glasgow.msc.in ${CMAKE_CURRENT_BINARY_DIR}/install/glasgow.msc @ONLY)

install(TARGETS fzn-glasgow RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR} COMPONENT minizinc)
# A static fzn-glasgow is self-contained, but a shared one needs the library
# beside it, and `--component minizinc` must install something that runs.
# minizinc-installed-msc is the test that notices.
if(GCS_SHARED_LIBRARY)
    install(TARGETS glasgow_constraint_solver LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR} COMPONENT minizinc)
endif()
install(DIRECTORY mznlib/ DESTINATION ${_gcs_mznlib_install_dir} COMPONENT minizinc)
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/install/glasgow.msc DESTINATION ${_gcs_msc_install_dir} COMPONENT minizinc)

# Installs the minizinc component into a scratch prefix and solves a model through
# the installed glasgow.msc, from a working directory where the relative paths
# resolve to nothing, so that only resolution against the .msc can succeed.
add_test(NAME minizinc-installed-msc COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_installed_msc_test.bash
    ${CMAKE_COMMAND} ${CMAKE_BINARY_DIR} $<CONFIG> ${CMAKE_CURRENT_BINARY_DIR}/installed-msc-prefix
    ${_gcs_msc_install_dir}/glasgow.msc ${CMAKE_SOURCE_DIR}/minizinc/tests/arithmetic/abs.mzn)
set_tests_properties(minizinc-installed-msc PROPERTIES SKIP_RETURN_CODE 66)

# The differential tests, one directory per global or family under tests/, each
# with its models and a CMakeLists.txt registering their lanes. Every lane runs
# in its own directory's build tree, and takes its test name as the name of its
# scratch files, so no two lanes can clobber each other's .fzn, output or proof.
#
# gcs_minizinc_test(<name> <model> <enumeration> <doproofs>
#                   [OPTIONS <harness option>...] [FLAGS <solverflags>]
#                   [REQUIRE <output regex>...])
#
# runs <model>, relative to the calling directory, through
# run_minizinc_test.bash, whose header documents the arguments: OPTIONS are its
# leading options (--fzn-pattern, --fzn-count, --reference-std and the rest),
# FLAGS its <solverflags>, and REQUIRE its <requiredpattern>s.
#
# A regex argument must have as many `[` as `]`, counting escaped ones. The
# arguments travel through CMake lists, and CMake does not split a list at a `;`
# inside square brackets, so an unbalanced `\[` silently glues the next argument
# onto the regex. The check below refuses that at configure time.
function(gcs_minizinc_test name model enumeration doproofs)
    if(ARGC GREATER 4)
        math(EXPR last "${ARGC} - 1")
        foreach(i RANGE 4 ${last})
            string(REGEX REPLACE "[^[]" "" opens "${ARGV${i}}")
            string(REGEX REPLACE "[^]]" "" closes "${ARGV${i}}")
            string(LENGTH "${opens}" opens)
            string(LENGTH "${closes}" closes)
            if(NOT opens EQUAL closes)
                message(FATAL_ERROR "gcs_minizinc_test(${name}): argument `${ARGV${i}}` has unbalanced square brackets")
            endif()
        endforeach()
    endif()
    cmake_parse_arguments(PARSE_ARGV 4 arg "" "FLAGS" "OPTIONS;REQUIRE")
    if(arg_UNPARSED_ARGUMENTS)
        message(FATAL_ERROR "gcs_minizinc_test(${name}): unexpected arguments ${arg_UNPARSED_ARGUMENTS}")
    endif()
    set(trailing)
    if(DEFINED arg_FLAGS OR arg_REQUIRE)
        set(trailing "${arg_FLAGS}" ${arg_REQUIRE})
    endif()
    add_test(NAME ${name} COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash ${arg_OPTIONS}
        $<TARGET_FILE:fzn-glasgow> ${CMAKE_CURRENT_SOURCE_DIR}/${model} ${name} ${enumeration} ${doproofs} ${trailing})
    set_tests_properties(${name} PROPERTIES SKIP_RETURN_CODE 66)
endfunction()

# gcs_fzn_json_test(<name> <fzn>) runs hand-written JSON FlatZinc straight
# through fzn-glasgow, for front-end paths no .mzn model can reach; see
# run_fzn_json_test.bash. The expected output is <fzn> with .expected for .fzn.
function(gcs_fzn_json_test name fzn)
    add_test(NAME ${name} COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_fzn_json_test.bash
        $<TARGET_FILE:fzn-glasgow> ${CMAKE_CURRENT_SOURCE_DIR}/${fzn} ${name})
endfunction()

add_subdirectory(tests/all_different)
add_subdirectory(tests/all_equal)
add_subdirectory(tests/among)
add_subdirectory(tests/arg_sort)
add_subdirectory(tests/arithmetic)
add_subdirectory(tests/bin_packing)
add_subdirectory(tests/circuit)
add_subdirectory(tests/comparison)
add_subdirectory(tests/count)
add_subdirectory(tests/cumulative)
add_subdirectory(tests/dag)
add_subdirectory(tests/diffn)
add_subdirectory(tests/disjunctive)
add_subdirectory(tests/element)
add_subdirectory(tests/global_cardinality)
add_subdirectory(tests/increasing)
add_subdirectory(tests/inverse)
add_subdirectory(tests/knapsack)
add_subdirectory(tests/lex)
add_subdirectory(tests/linear)
add_subdirectory(tests/logical)
add_subdirectory(tests/mdd)
add_subdirectory(tests/member)
add_subdirectory(tests/models)
add_subdirectory(tests/nvalue)
add_subdirectory(tests/objective)
add_subdirectory(tests/path)
add_subdirectory(tests/reachable)
add_subdirectory(tests/reader)
add_subdirectory(tests/regular)
add_subdirectory(tests/search)
add_subdirectory(tests/seq_precede_chain)
add_subdirectory(tests/sets)
add_subdirectory(tests/sort)
add_subdirectory(tests/subgraph)
add_subdirectory(tests/symmetric_all_different)
add_subdirectory(tests/table)
add_subdirectory(tests/tree)
add_subdirectory(tests/value_precede)
