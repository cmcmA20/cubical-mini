AGDA_BIN?=agda
AGDA_FLAGS?=-W error
AGDA_EXEC?=$(AGDA_BIN) $(AGDA_FLAGS)
FIX_WHITESPACE?=fix-whitespace
RTS_OPTIONS=+RTS -H3G -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)
RUNHASKELL?=runhaskell
EVERYTHINGS=$(RUNHASKELL) ./Everythings.hs
DATA_INSTANCE_DIRS=`find src/Data -type d -name Instances -printf "Data/%P\n"`
STR_INSTANCE_DIRS=`find src/Structures -type d -name Instances -printf "Structures/%P\n"`
CON_INSTANCE_DIRS=`find src/Containers -type d -name Instances -printf "Containers/%P\n"`

.PHONY : all
all : build

.PHONY : build
build :
	$(MAKE) AGDA_EXEC=$(AGDA_BIN) gen-everythings check

.PHONY : test
test : check-whitespace gen-inst-everythings gen-and-check-everythings check-README check

# checking and fixing whitespace

.PHONY : fix-whitespace
fix-whitespace:
	$(FIX_WHITESPACE)

.PHONY : check-whitespace
check-whitespace:
	$(FIX_WHITESPACE) --check

# checking and generating Everything files

.PHONY : check-everythings
check-everythings:
	$(EVERYTHINGS) check-except System

.PHONY : gen-inst-everythings
gen-inst-everythings:
	$(EVERYTHINGS) gen-public $(DATA_INSTANCE_DIRS)
	$(EVERYTHINGS) gen-public $(STR_INSTANCE_DIRS)
	$(EVERYTHINGS) gen-public $(CON_INSTANCE_DIRS)
	$(EVERYTHINGS) gen-public Truncation/Propositional/Instances

.PHONY : gen-everythings
gen-everythings:
	$(EVERYTHINGS) gen-except Foundations Meta
	$(EVERYTHINGS) gen-public Meta

.PHONY : gen-and-check-everythings
gen-and-check-everythings: gen-everythings check-everythings

.PHONY : check-README
check-README:
	$(EVERYTHINGS) check-README

# typechecking and generating listings for all files imported in README

.PHONY : check
check: gen-everythings
	$(AGDA) src/README.agda

.PHONY : timings
timings: clean gen-everythings
	$(AGDA) -v profile.modules:10 src/README.agda

.PHONY : listings
listings: $(wildcard src/**/*.agda)
	$(AGDA) -i. -isrc --html src/README.agda -v0

.PHONY : clean
clean:
	find . -type f -name '*.agdai' -delete

.PHONY: debug
debug : ## Print debug information.
	@echo "AGDA_BIN              = $(AGDA_BIN)"
	@echo "AGDA_FLAGS            = $(AGDA_FLAGS)"
	@echo "AGDA_EXEC             = $(AGDA_EXEC)"
	@echo "AGDA                  = $(AGDA)"
