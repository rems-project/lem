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

all: $(MACHINEFILES) generated
	$(TOOLDIR)/lem -ocaml -tex -lib $(TOOLDIR)/library bitwiseCompatibility.lem $(MACHINEFILES)
	mv *.ml generated/
	mv *.tex generated/

isabelle: $(MACHINEFILES) generated
	$(TOOLDIR)/lem -isa -lib $(TOOLDIR)/library bitwiseCompatibility.lem $(MACHINEFILES)
	make patch # apply patches
	mv *.thy generated/

generated:
	mkdir -p generated

patch:
# Isabelle/HOL gets stuck on ppc_sem_of_instruction otherwise
	sed 's/fun ppc_sem_of_instruction/primrec ppc_sem_of_instruction/'  \
	  MachineDefInstructionSemantics.thy                              \
	  > MachineDefInstructionSemanticsPatched.thy

# Patch to Bug #81 ( https://bitbucket.org/Peter_Sewell/lem/issue/81/isabelle-backend-does-not-rename )
	sed 's/declare is_isync.simps/declare is_isync0.simps/' \
	  MachineDefAxiomaticCore.thy \
	  > MachineDefAxiomaticCorePatched.thy
	mv MachineDefInstructionSemanticsPatched.thy \
	   MachineDefInstructionSemantics.thy
	mv MachineDefAxiomaticCorePatched.thy        \
	   MachineDefAxiomaticCore.thy
