COLM_BIN    = ../../colm/colm
COLM_LA     = ../../colm/libcolm.la
COLM_LIBDEP = $(COLM_LA)
COLM_BINDEP = $(COLM_BIN)

bin_PROGRAMS = ragel-java

ragel_java_CPPFLAGS = -I$(top_srcdir)/aapl -I$(top_srcdir)/ragel -I$(top_srcdir)/colm/include

dist_ragel_java_SOURCES = main.cc rlhc.c

nodist_ragel_java_SOURCES = \
	rlparse.c rlreduce.cc

ragel_java_LDADD = ../libragel.la ../libfsm.la $(COLM_LA)

BUILT_SOURCES = rlparse.c rlreduce.cc rlhc.c

EXTRA_DIST = rlparse.lm rlhc.lm

rlparse.c: rlparse.lm $(COLM_BINDEP)
	$(COLM_BIN) -I.. -c -b rlparseJava -o $@ -m rlreduce.cc $<

rlreduce.cc: rlparse.c

rlhc.c: rlhc.lm ../ril.lm $(COLM_BINDEP)
	$(COLM_BIN) -I.. -c -b rlhcJava -o $@ $<
