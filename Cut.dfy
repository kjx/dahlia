
//imported from dafny/dahlia=-11.dfy

//more or less replaces but CutTrunkBranch  below
method CutCore(cut : Object, tree : set<Object>)  returns (trunk : set<Object>, branch : set<Object>)
  requires cut in tree
  ensures  branch == set o <- tree |     inside(o,cut)  :: o
  ensures  trunk ==  set o <- tree | not(inside(o,cut)) :: o
  ensures  tree == branch + trunk + {}
  ensures  branch !! trunk

 // ensures forall o <- tree :: unchanged(o)
  ensures unchanged(tree) == (forall o <- tree :: unchanged(o))
  ensures unchanged(tree`fields)
 
  //reads tree
  modifies {}
  { 
    branch := set o <- tree | inside(o,cut) :: o;
    trunk := tree - branch;
  }




//do I want this one? 
///apprently tis the sam4 as CutCore --- 
function {:done} CutTrunkBranch(cut : Object, tree : set<Object>) : (r : (set<Object>,  set<Object>) )
  requires cut in tree
  ensures  r.1 == set o <- tree |     inside(o,cut)  :: o
  ensures  r.0 ==  set o <- tree | not(inside(o,cut)) :: o
  ensures  tree == r.1 + r.0 + {}
  { 
    var branch := set o <- tree | inside(o,cut) :: o;
    var trunk := tree - branch;
    (trunk, branch)
  }









lemma {:timeLimit 15}
CutIsCut(cut : Object, tree : set<Object>, trunk : set<Object>, branch : set<Object>)
  requires cut in tree
  requires branch == set o <- tree |     inside(o,cut)  :: o
  requires trunk ==  set o <- tree | not(inside(o,cut)) :: o
  requires tree == branch + trunk
  requires branch !! trunk

  requires forall o <- tree :: o.Ready() && o.Valid()
  ensures  forall o <- tree :: (o in branch) !=  (o in trunk)
  ensures  edges(tree) == edges(trunk) + edges(branch)
{
  assert branch !! trunk;
  assert tree == branch + trunk;
  assert forall o <- tree :: (o in branch) !=  (o in trunk);

  assert trunk <= tree;

  assert tree == trunk + branch;
  assert edges(tree) == edges(trunk) + edges(branch);
}

// {:timeLimit 60}
lemma {:vcs_split_on_every_assert} {:timeLimit 60}
CutIsCut2(cut : Object, tree : set<Object>, trunk : set<Object>, branch : set<Object>)
  requires forall o <- tree :: o.Ready() && o.Valid()
  requires cut in tree
  requires branch == set o <- tree |     inside(o,cut)  :: o
  requires trunk ==  set o <- tree | not(inside(o,cut)) :: o
  requires tree == branch + trunk
  requires branch !! trunk

  requires forall o <- tree :: (o in branch) !=  (o in trunk)
  requires edges(tree) == edges(trunk) + edges(branch)

  requires OutgoingReferencesAreInTheseObjects(tree)
  requires StandaloneObjectsAreValid(tree)

  ensures forall f <- trunk, t <- f.outgoing()
  :: (t in trunk) || (t == cut)

  ensures OutgoingReferencesFromTheseObjectsAreToTheseObjects(trunk, trunk+{cut}) 
{
   forall f <- tree, t <- f.outgoing()   //yeah could've just looked at the trunk .
   //  | f.owner.Heap? && t.owner.Heap? && cut.owner.Heap?  ///if it's world, it's not a (big) problem
   // ensures OutgoingReferencesAreInTheseObjects(trunk)   ///shouldn't verify: no  easy wayh to say "trunk+cut(with no fields)"
    ensures (f in trunk) ==> ((t in trunk) || t == cut)
    //   ensures true
   {
      assert refOK(f,t);
     // assert t.owner.Heap? && inside(f,t.owner); //just cos

      if (t == cut) //then we're OK
         { assert t == cut;   //cos dafnt wants something there...
      } else {
      if (inside(f,cut)) //then we don't have to care
       {
        assert f in branch;  //so let's not
      } else {
        assert f in trunk;
        if (not(inside(t, cut))) {
          assert t in trunk;  //also don't have to care   
        } else {
          //so this is the problematic case ]
          assert f in trunk;
          assert inside(t, cut);

          if (ownerInsideOwner(t.owner, {cut}) && t != cut) {        
            assert refOK(f,t);
            assert {:contradiction} ownerInsideOwner({f},t.owner);
            transitiveInsideOwners({f}, t.owner, {cut});
            assert {:contradiction} inside(f,cut);
            assert false;
          } else {
            assert f in trunk;
            assert inside(t, cut);

   assert t.Ready();
   assert inside(t, cut);
   assert t != cut;

            // InsideIsHeap(t, cut);
            assert not(ownerInsideOwner(t.owner, {cut})  && t != cut  );
            assert not(ownerInsideOwner(t.owner, {cut})) || t == cut;
    //        JimmySavilleIsAPaedo(f,t,cut,tree,trunk,branch);
            assert t == cut; 
          }
         } 
       } 
      }
    assert (f in trunk) ==> ((t in trunk) || t == cut);
    assert derek: (f in trunk) ==> ((t in trunk) || t == cut);
    reveal derek;
   }  // end forall


//  forall f <- tree, t <- f.outgoing()   //yeah could've just looked at the trunk \.
//      | f.owner.Heap? && t.owner.Heap? && cut.owner.Heap?  ///if it's world, it's not a (big) problem
//    // ensures OutgoingReferencesAreInTheseObjects(trunk)   ///shouldn't verify: no  easy wayh to say "trunk+cut(with no fields)"
//     ensures (f in trunk) ==> ((t in trunk) || t == cut)
//     {
//      // reveal derek;
//     }

     forall f <- trunk, t <- f.outgoing()   //yeah could've just looked at the trunk \.
  //   | f.owner.Heap? && t.owner.Heap? && cut.owner.Heap?  ///if it's world, it's not a (big) problem
   // ensures OutgoingReferencesAreInTheseObjects(trunk)   ///shouldn't verify: no  easy wayh to say "trunk+cut(with no fields)"
    ensures (t in trunk || t == cut)
    {
     // reveal derek;
    }
  // assert forall f <- tree, t <- f.outgoing()
  //    |  f.owner.Heap? && t.owner.Heap? && cut.owner.Heap?
  //    :: (f in trunk) ==> ((t in trunk) || t == cut);

  // assert forall f <- trunk, t <- f.outgoing()
  //  |  f.owner.Heap? && t.owner.Heap? && cut.owner.Heap?  
  //  :: (t in trunk || t == cut);
} // end lemma

////////////////////////////////////////////////////////////////////////
//             transitiveInside(t, t.owner, cut);
//     (inside(f,t.owner))
// )        
//         transitiveInside(t, t.owner, cut);
//         assert inside(t,cut);
//         assert t in branch;
//         assert t !in trunk;
//         assert false;
//         } else {
//             assert not( inside(t.owner, cut) ); 
//
//             if ( assert inside(t, cut);
//             assert not(inside(t.owner, cut));
//             JimmySavilleIsAPaedo(f,t,cut,tree,trunk,branch);
//             assert t == cut;
////////////////////////////////////////////////////////////////////////

//attempt at proof by contradiction
//1am Sun 17 Dec, this seems to work., and prove waht we want? Kinda?
// lemma JimmySavilleIsAPaedo(f : Object, t : Object, cut : Object, tree : set<Object>, trunk : set<Object>, branch : set<Object>)
//   requires cut in tree
//   requires branch == set o <- tree |     inside(o,cut)  :: o
//   requires trunk ==  set o <- tree | not(inside(o,cut)) :: o
//   requires tree == branch + trunk + {}
//   requires branch !! trunk
// 
//   requires f in tree
//   requires t in tree
// 
//   // requires f.owner.Heap?
//   // requires t.owner.Heap?
//   // requires cut.owner.Heap?
// 
//   //  requires f.Valid() && t.Valid() && cut.Valid()
//   requires f.Ready() && t.Ready() && cut.Ready()
//   requires inside(t, cut)
//   requires not(ownerInsideOwner(t.owner, {cut}))
// 
//   // requires OutgoingReferencesAreInTheseObjects(tree)
//   // requires StandaloneObjectsAreValid(tree)
//  
//   requires f != t //&& f != cut //&& t != cut
//   /// requires OutgoingReferencesAreInTheseObjects(tree)
//   //
//  
//   ensures t == cut
// {
// 
//   // assert t.owner.Heap?;
//   // assert inside(t, t.owner); //duh. but not sure ir it really cattures what we most want
// 
//   assert ownerInsideOwner({t}, t.owner); //see abnove comment
// 
//   if (t == cut)
//    { assert inside(t, cut); return; }
// 
//   assert t != cut;
// 
// //  if (t.owner == cut)    { assert inside(t, cut); return; }
// 
// if (inside(t,cut)) { return; }
// 
// 
//   assert t != cut;
// //  assert t.owner != {cut};  //ALOBST CERTIAWEON
// 
//   if (ownerInsideOwner (t.owner, {cut}))
//         { transitiveInsideOwners({t}, t.owner, {cut});
//            assert inside(t, cut); return; }
// //  else {
// // assert ! (inside(t, cut)); return; }
//    
// 
// // deleting all the following linese saves - 3 seconds!   
//  assert t != cut;
//  assert flattenAMFOs(t.owner) != cut.AMFO;
//  assert not(ownerInsideOwner (t.owner, {cut}));
// 
// assert ! (ownerInsideOwner (t.owner, {cut})) && t != cut ==> ! (inside(t, cut));
// 
// assert ! (inside(t, cut));
// 
// 
// }

lemma {:vcs_split_on_every_assert}
CuttyOne(cut : Object, tree : set<Object>, trunk : set<Object>, branch : set<Object>)

  requires cut in tree
  requires branch == set o <- tree |     inside(o,cut)  :: o
  requires trunk ==  set o <- tree | not(inside(o,cut)) :: o
  requires tree == branch + trunk
  requires branch !! trunk

  ensures  trunk <= tree
  ensures  edges(trunk) <= edges(tree)

  requires 
    && (forall o <- tree :: o.Ready() && o.Valid())
    && StandaloneObjectsAreValid(tree)
    && OutgoingReferencesAreInTheseObjects(tree)
    && IncomingReferencesConstraintsOK(edges(tree))  

  ensures 
    && (forall o <- trunk :: o.Ready() && o.Valid())
    && StandaloneObjectsAreValid(trunk)
  //   //&& OutgoingReferencesAreInTheseObjects(trunk) //this is too much - see below
    && OutgoingReferencesFromTheseObjectsAreToTheseObjects(trunk,  trunk+{cut})
 
  
    && IncomingReferencesConstraintsOK(edges(trunk))  

{ //kyfny can verify this without any code in here - 4.6.0 crashes without it
    CutIsCut(cut,tree,trunk,branch);
    CutIsCut2(cut,tree,trunk,branch);

    var less := edges(trunk);
    var more := edges(tree);
    var lesp := partitionedIncomingEdges(less);
    var morp := partitionedIncomingEdges(more);
   
    FewerPartitionedIncomingEdgesValid(less, more, lesp, morp);
}


lemma // {:timeLimit 60}
CuttyOwnerisUnique  (cut : Object, tree : set<Object>, trunk : set<Object>, branch : set<Object>,
                   o : Object, f : string, lesp : map<Object,set<Edge>>)

  requires o in tree
  requires o in trunk
  requires f in o.fieldModes
  requires f in o.fields
  requires o.fieldModes[f].Owned?
  requires cut == o.fields[f]

  requires lesp == partitionedIncomingEdges(edges(trunk))
  requires 
    && (forall o <- trunk :: o.Ready() && o.Valid())
    && StandaloneObjectsAreValid(trunk)
    //&& OutgoingReferencesAreInTheseObjects(trunk) //this is too much - see below
    && OutgoingReferencesFromTheseObjectsAreToTheseObjects(trunk,  trunk+{cut})
    && IncomingReferencesConstraintsOK(edges(trunk))

  ensures       cut in lesp.Keys
 ensures  lesp[cut] == {Edge(o,f,o.fieldModes[f],cut)}
  ensures |lesp[cut]| == 1

// //more consequences...

    ensures (forall o <- lesp.Keys :: 
      (exists e : Edge <- lesp[o] :: e.m.Owned?) ==> (
         // ((|partition[o]|) <= 1) 
         GroundSingleton( lesp[o] )  ))
  

    ensures (forall o <- lesp.Keys :: 
      (exists e : Edge <- lesp[o] :: e.m.Owned?) ==> 
         (|lesp[o]|) == 1)

    ensures |lesp[cut]| == 1
    ensures edge(o,f) in lesp[cut]
    ensures lesp[cut] == {edge(o,f)}
{
    var es := edges(trunk);
// //    assert forall e <- es :: (e.f == o && e.n == f) ==> e.m == o.fieldModes[f] && e.t == o.fields[f];

  
//     //what all this says is that it would be nice (more than nice)
//     //if we updated objects with the status (as well as incoming references :-)
//     //so we'd kow cut was unique if it's owned. 

//     assert o in trunk;
//     assert f in o.fields;
//     assert o.fieldModes[f].Owned?;
//     edgesWork(trunk, edges(trunk)); edgesWorks2(trunk, edges(trunk)); 
//     assert exists e <- edges(trunk) :: e.f == o && e.n == f;

//     assert forall e <- edges(trunk) :: (e.t in lesp) && (e in lesp[e.t]);  
   
//     assert o in trunk;
//     assert forall o <- trunk, f <- (o.fields.Keys * o.fieldModes.Keys) :: 
//       Edge(o,f,o.fieldModes[f],o.fields[f]) in edges(trunk);
//     assert forall o <- trunk, f <- (o.fields.Keys * o.fieldModes.Keys) :: 
//       Edge(o,f,o.fieldModes[f],o.fields[f]) in lesp[o.fields[f]];

//     assert o.fields[f] in lesp.Keys; 
//     assert f in o.fields;
//     assert  Edge(o,f,o.fieldModes[f],o.fields[f]) in edges(trunk);
//     assert  Edge(o,f,o.fieldModes[f],o.fields[f]) in  lesp[o.fields[f]];
//     assert cut == o.fields[f];
//     assert  Edge(o,f,o.fieldModes[f],cut) in  lesp[cut];
//     assert o.fieldModes[f].Owned?;
//     assert  Edge(o,f,o.fieldModes[f],cut) in  lesp[cut];


assert cut == o.fields[f];
assert edge(o,f) in es;
assert edge(o,f) in lesp[cut];
assert OneOwnerIncoming(lesp);  //be good to ahve a version of IncmingReferencesConstraintsOK,... ConstraintsOKIncoming
assert edge(o,f).m.Owned?;
assert {edge(o,f)} == lesp[cut];
assert cut in lesp.Keys;  //dug
 

//    {
//       var partition := lesp;
//  assert (forall o <- partition.Keys :: 
//       (exists e <- partition[o] :: e.m.Owned?) ==> (
//          // ((|partition[o]|) <= 1) 
//          GroundSingleton( partition[o] )  ));
//            //if there's an Owner, it should be the *only* reference (could be XU but isn't...)
 

//  assert (forall o <- partition.Keys :: 
//       (exists e <- partition[o] :: e.m.Owned?) ==> (
//          ((|partition[o]|) <= 1)));
//    }

//     assert (forall o <- lesp.Keys :: 
//       (exists e : Edge <- lesp[o] :: e.m.Owned?) ==> (
//          // ((|partition[o]|) <= 1) 
//          GroundSingleton( lesp[o] )  ));
  

//     assert (forall o <- lesp.Keys :: 
//       (exists e : Edge <- lesp[o] :: e.m.Owned?) ==> 
//          (|lesp[o]|) == 1);

//     assert |lesp[cut]| == 1;
//     var eee := Edge(o,f,o.fieldModes[f],cut);
//     assert eee in lesp[cut];
//     IAmTheOnlyOne(eee,lesp[cut]);
//     assert lesp[cut] == {eee};
//     assert lesp[cut] == {Edge(o,f,o.fieldModes[f],cut)};

}













lemma OwnersAreNotCut1(o : Object, cut : Object, os : set<Object>) 
   requires o in os
   requires cut in os
   requires not(inside(o, cut))
   requires o.Ready() && cut.Ready()
   requires forall owner <- o.AMFO ::     inside(o,owner)
   ensures  forall owner <- o.AMFO :: not(inside(owner,cut))
  {
     //attempted contradiction
    if (exists owner <- o.AMFO :: o.Ready() && inside(owner,cut)) 
     {
         var owner :| owner in o.AMFO && o.Ready() && inside(owner,cut);
         assert owner in o.AMFO;
         assert inside(o,owner);
         assert inside(owner,cut);
         assert inside(o,cut) by {transitiveInside(o,owner,cut);}
         assert false;
     }

    assert not(exists owner <- o.AMFO ::  inside(owner,cut));
    assert forall owner <- o.AMFO ::  not(inside(owner,cut));
  }

