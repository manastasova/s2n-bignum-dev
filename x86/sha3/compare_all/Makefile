# Makefile for Keccak-f1600x4 Implementation Test & Benchmark Suite

CC = gcc
CFLAGS = -mavx2 -O3 -Wall
LDFLAGS = -lm

# Macros required for the implementations
COMMON_DEFINES = -DMLK_FIPS202_X86_64_XKCP \
                 -DMLK_ALIGN="__attribute__((aligned(32)))" \
                 -DMLK_EMPTY_CU\(x\)=

# Final implementation needs additional defines for little-endian
FINAL_DEFINES = $(COMMON_DEFINES) -DMLK_SYS_LITTLE_ENDIAN

# Source files (numbered naming scheme)
ORG_SRC = 1_KeccakP_1600_times4_SIMD256_org_standalone.c
RC_TABLE_SRC = 2_KeccakP_1600_times4_SIMD256_rc_table.c
NO_SPECIAL_RHO_SRC = 3_KeccakP_1600_times4_SIMD256_no_special_rho.c
NO_THETA_PREPS_SRC = 4_KeccakP_1600_times4_SIMD256_no_theta_preps.c
UPDATE_LOAD_SRC = 5_KeccakP_1600_times4_SIMD256_update_load.c
X2_UNROLLED_SRC = 6_KeccakP_1600_times4_SIMD256_x2_unrolled.c
LOOP_SRC = 7_KeccakP_1600_times4_SIMD256_loop.c
X2_UNROLLED_ONE_ARG_SRC = 8_KeccakP_1600_times4_SIMD256_x2_unrolled_once_arg.c
X2_UNROLLED_ONE_ARG_SPECIAL_RHO_SRC = 9_KeccakP_1600_times4_SIMD256_x2_unrolled_once_arg_special_rho.c
LOOP_SPECIAL_RHO_SRC = 10_KeccakP_1600_times4_SIMD256_loop_special_rho.c
X2_ADDS_SRC = 11_KeccakP_1600_times4_SIMD256_x2_unrolled_once_arg_special_rho_adds.c
TEST_SRC = test_all_implementations.c

# Object files
ORG_OBJ = 1_KeccakP_1600_times4_SIMD256_org_standalone.o
RC_TABLE_OBJ = 2_KeccakP_1600_times4_SIMD256_rc_table.o
NO_SPECIAL_RHO_OBJ = 3_KeccakP_1600_times4_SIMD256_no_special_rho.o
NO_THETA_PREPS_OBJ = 4_KeccakP_1600_times4_SIMD256_no_theta_preps.o
UPDATE_LOAD_OBJ = 5_KeccakP_1600_times4_SIMD256_update_load.o 
X2_UNROLLED_OBJ = 6_KeccakP_1600_times4_SIMD256_x2_unrolled.o
LOOP_OBJ = 7_KeccakP_1600_times4_SIMD256_loop.o
X2_UNROLLED_ONE_ARG_OBJ = 8_KeccakP_1600_times4_SIMD256_x2_unrolled_once_arg.o
X2_UNROLLED_ONE_ARG_SPECIAL_RHO_OBJ = 9_KeccakP_1600_times4_SIMD256_x2_unrolled_once_arg_special_rho.o
LOOP_SPECIAL_RHO_OBJ = 10_KeccakP_1600_times4_SIMD256_loop_special_rho.o
X2_ADDS_OBJ = 11_KeccakP_1600_times4_SIMD256_x2_unrolled_once_arg_special_rho_adds.o

# All object files
OBJS = $(ORG_OBJ) $(RC_TABLE_OBJ) $(NO_SPECIAL_RHO_OBJ) $(NO_THETA_PREPS_OBJ) $(UPDATE_LOAD_OBJ) $(X2_UNROLLED_OBJ) $(LOOP_OBJ) $(X2_UNROLLED_ONE_ARG_OBJ) $(X2_UNROLLED_ONE_ARG_SPECIAL_RHO_OBJ) $(LOOP_SPECIAL_RHO_OBJ) $(FINAL_OBJ) $(X2_ADDS_OBJ)

# Target executable
TARGET = test_all_implementations

.PHONY: all clean run help

all: $(TARGET)

$(TARGET): $(TEST_SRC) $(OBJS)
	$(CC) $(CFLAGS) -o $@ $(TEST_SRC) $(OBJS) $(LDFLAGS)

$(ORG_OBJ): $(ORG_SRC)
	$(CC) $(CFLAGS) $(COMMON_DEFINES) -c $< -o $@

$(RC_TABLE_OBJ): $(RC_TABLE_SRC)
	$(CC) $(CFLAGS) -c $< -o $@

$(NO_SPECIAL_RHO_OBJ): $(NO_SPECIAL_RHO_SRC)
	$(CC) $(CFLAGS) -c $< -o $@

$(NO_THETA_PREPS_OBJ): $(NO_THETA_PREPS_SRC)
	$(CC) $(CFLAGS) -c $< -o $@

$(UPDATE_LOAD_OBJ): $(UPDATE_LOAD_SRC)
	$(CC) $(CFLAGS) -c $< -o $@

$(X2_UNROLLED_OBJ): $(X2_UNROLLED_SRC)
	$(CC) $(CFLAGS) -c $< -o $@

$(LOOP_OBJ): $(LOOP_SRC)
	$(CC) $(CFLAGS) -c $< -o $@

$(X2_UNROLLED_ONE_ARG_OBJ): $(X2_UNROLLED_ONE_ARG_SRC)
	$(CC) $(CFLAGS) -c $< -o $@

$(X2_UNROLLED_ONE_ARG_SPECIAL_RHO_OBJ): $(X2_UNROLLED_ONE_ARG_SPECIAL_RHO_SRC)
	$(CC) $(CFLAGS) -c $< -o $@

$(LOOP_SPECIAL_RHO_OBJ): $(LOOP_SPECIAL_RHO_SRC)
	$(CC) $(CFLAGS) -c $< -o $@

$(FINAL_OBJ): $(FINAL_SRC) KeccakP_1600_times4_SIMD256.h
	$(CC) $(CFLAGS) $(FINAL_DEFINES) -c $< -o $@

$(X2_ADDS_OBJ): $(X2_ADDS_SRC)
	$(CC) $(CFLAGS) -c $< -o $@

run: $(TARGET)
	./$(TARGET)

clean:
	rm -f $(OBJS) $(TARGET)

help:
	@echo "Available targets:"
	@echo "  all    - Build the test executable (default)"
	@echo "  run    - Build and run the tests"
	@echo "  clean  - Remove built files"
	@echo "  help   - Show this help message"
	@echo ""
	@echo "Usage examples:"
	@echo "  make              # Build the executable"
	@echo "  make run          # Build and run tests"
	@echo "  ./$(TARGET)       # Run all tests"
	@echo "  ./$(TARGET) org          # Test only 'org' implementation"
	@echo "  ./$(TARGET) rc_table     # Test only 'rc_table' implementation"
	@echo "  ./$(TARGET) no_theta_preps # Test only 'no_theta_preps'"
	@echo "  ./$(TARGET) update_load  # Test only 'update_load'"
	@echo "  ./$(TARGET) -5000        # Use 5000 repetitions"
