# dahlia
heap models in dafny

currently being refactored out of dahlia-20.dfy into other files...

still to do for refactoring:
 - deal with the whole AOK shit
 - walkies clean is in terms of AOK :-()
 - walkiesIsoOK, isIsomorphicMappingOWNED
 - edgesAreConsistentWithDafnyHeap
 - LosingMyEdge


// shit still to do
// - copyable flag
// - outgoing references
// - owners for stack frames
// - translate fieldModes
// - translate owners
// - borrow field mode - currently switched off/
// - (drop flag)

//can we do a depressing check that goes throught the mapping, say
//and for each key wants a unqiue domain object,
//where each owber & fiend value isa key???



// dahlia-20c - offline version to fiddle with decreases clauses
// dahlia-20b - file -verifies 4mins nightly 2024-07-17-91d35a2  - BUT with two assumes...
// dahlia-20a - Clone-field-map cerifies!!!  
// dahlia-20g - ditto.  also make fails, don't give a shit. 
// dahlia-20f-fields - Clone_Field-Map verifies (but Clone_Via-Map no longer doe)
// dahlia-20 - working on clone via map for fields
// dahlia-19 - attempt to fix Clone_Via_Map which started timing out for no reason...
// dahlia-18 - version that proces (mostly) including process one field
// dahlia-17g - alternative approach to putALLOutside
// dahlia-17f - giving up on putALLOutside...
// dahlia-17d and *putAllOutside* 
// dahlia-17 both putInside and putOutside
// dahlia-16 has Map dataype-based cloning for working for putOutside
// dahlia-15 working on cloning fields
// dahlia-14 runs & verifies whole file..  thu 14 may 

//compiles 15s --- Fri 10 May ---- date; time nightly  verify  dahlia-11-nopaque-objectonly.dfy   --isolate-assertions --verification-time-limit 15 --cores 8   --log-format "text;LogFileName=log.txt" ; date; say done 
//compiles & verifies --- 25 Jul 2025 --- 4m37s, Dafny program verifier finished with 8918 verified, 0 errors  --isolate-assertions --verification-time-limit 15 --cores 8  
