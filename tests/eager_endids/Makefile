.include "../../share/mk/top.mk"

TEST.tests/eager_endids != ls -1 tests/eager_endids/eager_endids*.c
TEST_SRCDIR.tests/eager_endids = tests/eager_endids
TEST_OUTDIR.tests/eager_endids = ${BUILD}/tests/eager_endids

.for n in ${TEST.tests/eager_endids:T:R:C/^eager_endids//}
INCDIR.${TEST_SRCDIR.tests/eager_endids}/eager_endids${n}.c += src/adt
.endfor

SRC += ${TEST_SRCDIR.tests/eager_endids}/utils.c

.for n in ${TEST.tests/eager_endids:T:R:C/^eager_endids//}
test:: ${TEST_OUTDIR.tests/eager_endids}/res${n}
SRC += ${TEST_SRCDIR.tests/eager_endids}/eager_endids${n}.c
CFLAGS.${TEST_SRCDIR.tests/eager_endids}/eager_endids${n}.c += -UNDEBUG

${TEST_OUTDIR.tests/eager_endids}/run${n}: ${TEST_OUTDIR.tests/eager_endids}/eager_endids${n}.o ${TEST_OUTDIR.tests/eager_endids}/utils.o ${BUILD}/lib/libfsm.a ${BUILD}/lib/libre.a
	${CC} ${CFLAGS} ${CFLAGS.${TEST_SRCDIR.tests/eager_endids}/eager_endids${n}.c} -o ${TEST_OUTDIR.tests/eager_endids}/run${n} ${TEST_OUTDIR.tests/eager_endids}/eager_endids${n}.o ${TEST_OUTDIR.tests/eager_endids}/utils.o ${BUILD}/lib/libfsm.a ${BUILD}/lib/libre.a
${TEST_OUTDIR.tests/eager_endids}/res${n}: ${TEST_OUTDIR.tests/eager_endids}/run${n}
	( ${TEST_OUTDIR.tests/eager_endids}/run${n} 1>&2 && echo PASS || echo FAIL ) > ${TEST_OUTDIR.tests/eager_endids}/res${n}
.endfor
