TOOLDIR=../..

# Order is significant!
MACHINEFILES=\
bitwiseCompatibility.lem\
machineDefUtils.lem \
machineDefFreshIds.lem \
machineDefValue.lem \
machineDefTypes.lem \
machineDefInstructionSemantics.lem \
machineDefStorageSubsystem.lem \
machineDefThreadSubsystem.lem \
machineDefSystem.lem \
machineDefAxiomaticCore.lem


all: $(MACHINEFILES)
	$(TOOLDIR)/lem -ocaml -tex -lib $(TOOLDIR)/library bitwiseCompatibility.lem $(MACHINEFILES)
	mkdir -p generated
	mv *.ml generated/
	mv *.tex generated/
