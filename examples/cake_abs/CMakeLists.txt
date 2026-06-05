add_executable(cake_abs cake_abs.cc)
target_link_libraries(cake_abs PRIVATE glasgow_constraint_solver)
target_link_libraries(cake_abs PRIVATE cxxopts)
target_link_libraries(cake_abs PRIVATE gcs_fmt)

# Exercises the full verified-encoding chain (solver -> cake_pb_cp -> veripb
# --elaborate -> cake_pb_cp) plus the opbdiff oracle. Requires the prebuilt
# cake_pb_cp (set CAKE_PB_CP) and veripb; the driver exits 77 to skip when those
# are absent, so this is a no-op on machines without them.
add_test(NAME cake_abs_verified_encoding
    COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/run_cake_pb_cp.bash $<TARGET_FILE:cake_abs>)
set_tests_properties(cake_abs_verified_encoding PROPERTIES SKIP_RETURN_CODE 77)
