#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

.PHONY: clean go

# Set ARCH to "x86" or "arm" as appropriate; this is literally the
# directory name in which the libs2nbignum.a file should be found.
# If this block fails to do it automatically, replace with manual
# setting: ARCH=x86 or ARCH=arm as appropriate

ARCH=unknown_architecture

UNAME_RESULT=$(shell uname -m)

ifeq ($(UNAME_RESULT),x86_64)
ARCH=x86
endif

ifeq ($(UNAME_RESULT),aarch64)
ARCH=arm
endif

ifeq ($(UNAME_RESULT),arm64)
ARCH=arm
endif

# Benchmarking progfram

# Reference kernels extracted from aws-lc, for head-to-head comparison only.
# They are NOT part of libs2nbignum.a and NOT covered by any proof; they are
# linked into the benchmark binary alone. ARM only.
REF_SRC = $(wildcard reference/*.S)
REF_OBJ = $(REF_SRC:.S=.o)

# Two reference kernels come from hanno-becker/aws-lc and #include openssl headers,
# so AWSLC_INC must point at an aws-lc checkout for those two to build.
AWSLC_INC ?= /home/ubuntu/aws-lc-all/aws-lc/include
reference/%.o: reference/%.S ; $(CC) -c -I../include -I$(AWSLC_INC) -o $@ $<

benchmark: benchmark.c ../include/s2n-bignum.h ../$(ARCH)/libs2nbignum.a $(REF_OBJ); $(CC) -O3 -o benchmark benchmark.c $(REF_OBJ) -L../$(ARCH) -ls2nbignum -lm

go: benchmark ; ./benchmark

clean: ; rm -f benchmark $(REF_OBJ)
