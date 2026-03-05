#
# Build tile.slang shaders into a slang module and copy to build output
#

glob_append(tile_shader_sources "*.slang")

# Set output directories for build tree
# Files go under a "slang/" subdirectory so that `import slang.tile;` resolves
# to <standard-module-dir>/slang/tile.slang-module at runtime.
set(tile_output_dir "${CMAKE_BINARY_DIR}/$<CONFIG>/${slang_library_dir}/${SLANG_STANDARD_MODULE_DIR_NAME}/slang")
set(tile_module_file "${tile_output_dir}/${SLANG_TILE_MODULE_FILE_NAME}")

# Copy tile shader files to output directory
set(tile_copied_files)
foreach(shader_file ${tile_shader_sources})
    get_filename_component(shader_name ${shader_file} NAME)
    set(dest_file "${tile_output_dir}/${shader_name}")
    add_custom_command(
        OUTPUT ${dest_file}
        COMMAND ${CMAKE_COMMAND} -E make_directory ${tile_output_dir}
        COMMAND ${CMAKE_COMMAND} -E copy ${shader_file} ${dest_file}
        DEPENDS ${shader_file}
        VERBATIM
    )
    list(APPEND tile_copied_files ${dest_file})
endforeach()

# Determine which compiler to use for building the module
# For cross-compilation, use slang-bootstrap from SLANG_GENERATORS_PATH
# (slang-bootstrap is a standalone tool with no external dependencies)
# Otherwise, use the slangc built as part of this build
if(SLANG_GENERATORS_PATH)
    if(CMAKE_HOST_WIN32)
        set(CMAKE_HOST_EXECUTABLE_SUFFIX ".exe")
    else()
        set(CMAKE_HOST_EXECUTABLE_SUFFIX "")
    endif()
    set(SLANG_COMPILER "${SLANG_GENERATORS_PATH}/slang-bootstrap${CMAKE_HOST_EXECUTABLE_SUFFIX}")
    set(SLANG_COMPILER_DEPENDENCY)
elseif(SLANG_ENABLE_SLANGC)
    set(SLANG_COMPILER slangc)
    set(SLANG_COMPILER_DEPENDENCY slangc)
else()
    # As a fallback, use the system-installed `slangc` compiler
    set(SLANG_COMPILER slangc)
    set(SLANG_COMPILER_DEPENDENCY)
endif()

# Determine compiler flags based on build type
if(SLANG_STANDARD_MODULE_DEVELOP_BUILD)
    set(TILE_MODULE_DEFINES "-DUNIT_TEST")
else()
    set(TILE_MODULE_DEFINES "")
endif()

# Build tile.slang-module and output to the output directory
add_custom_command(
    OUTPUT ${tile_module_file}
    COMMAND ${SLANG_COMPILER} ${TILE_MODULE_DEFINES} tile.slang -o ${SLANG_TILE_MODULE_FILE_NAME}
    DEPENDS ${tile_copied_files} ${SLANG_COMPILER_DEPENDENCY}
    WORKING_DIRECTORY ${tile_output_dir}
    VERBATIM
)

# Create a target to ensure the tile module is built
add_custom_target(
    slang-tile-module
    ALL
    DEPENDS ${tile_module_file}
)
set_target_properties(slang-tile-module PROPERTIES FOLDER generated)

# Install the tile directory to the configured location in the release package
# Installs into <install-dir>/slang/ to match the `import slang.tile;` convention.
install(
    DIRECTORY ${tile_output_dir}/
    DESTINATION ${SLANG_STANDARD_MODULE_INSTALL_DIR}/slang
    FILES_MATCHING
    PATTERN "*.slang"
    PATTERN "*.slang-module"
)
