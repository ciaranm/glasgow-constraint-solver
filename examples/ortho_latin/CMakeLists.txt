add_executable(ortho_latin ortho_latin.cc)
target_link_libraries(ortho_latin PRIVATE glasgow_constraint_solver)


target_link_libraries(ortho_latin PRIVATE cxxopts)

# Pin GAC here: the program now defaults to the non-GAC not-equals encoding, whose
# full-enumeration proof at this size is far larger than the GAC one this test expects.
add_test(NAME ortho_latin-5 COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:ortho_latin> --all-different gac 5)
