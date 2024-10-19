

    predicate IncomingReferencesConstraintsOK( es : set<Edge> )
      reads set e <- es :: e.f
      reads set e <- es :: e.t
      requires edgesAreConsistentWithDafnyHeap(es)
     reads set o <- e2o(es), o2 <- o.ValidReadSet() :: o2
    { 
     var partition := partitionedIncomingEdges(es);

      && OnlyOneOwnedOrLoanedIncoming(partition)
      && OneOwnerIncoming(partition)                   
      && BorrowedNotOwnedIncoming(partition)                
      && BorrowsLoansConsistentPermissionIncoming(partition)
      && OnlyOneWriterIncoming(partition)                   
    }





//ModeEdges --- currently WRONG 
//tnis stuff supersesded but still here...

const own1Predicate := ( m : Mode ) => m.Owned? || m.Loaned?

 predicate {:timeLimit 10}  OnlyOneOwner(es : set<Edge>)
       reads set e <- es :: e.f
      reads set e <- es :: e.t
      requires edgesAreConsistentWithDafnyHeap(es)
  // reads os, os`fieldModes
  //reads e2o(edges(os)) //because os may be "open" - may have oyutgoing references...
  //reads e2o(edges(os)) //because os may be "open" - may have oyutgoing references...
  //  reads set o <- os, o2 <- o.AMFO :: o2`fields
  //  reads (e2o(edges(os)))
  //  reads set o <- e2o(edges(os)), o2 <- o.AMFO :: o2`fields
  // //jaysur, marry, yosef & the wee fuken daankey
  // requires forall o <- e2o(edges(os)) :: o.Ready() && o.Valid()
  {
//o2e2o(os,edges(os));
   NoMoreThanOneIncomingEdges(own1Predicate, es)
  }

   
    predicate wrt1Predicate(m : Mode) { (m.Owned? && m.perm.Write?) || (m.Borrow? && m.perm.Write?) }
    predicate wrt2Predicate(m : Mode) { (m.Owned? || m.Borrow?) && m.perm.Write? }


 predicate OnlyOneWriter(es : set<Edge>)
       reads set e <- es :: e.f
      reads set e <- es :: e.t
      requires edgesAreConsistentWithDafnyHeap(es)
  //reads os, os`fieldModes 
  // reads e2o(edges(os))
  //reads  os +(set o <- os, o2 <- o.ValidReadSet() :: o2)
  //  requires forall o <- os :: o.Ready() && o.Valid()   //we don't care what's in the object at this point, do we?
  // I mean: might be asier if we tadde objects as unique within a region, ut...
 {
   NoMoreThanOneIncomingEdges(wrt1Predicate, es)
 }

  //  function ModeEdges(pred : Mode -> bool, es : set<Edge>) : set<Edge>
  //   //  reads os, os`fieldModes
  //  //reads e2o(es)
  //   {
  //     set e <- es | pred(e.m) :: e
  //   } 




   predicate NoMoreThanOneIncomingEdges(pred : Mode -> bool, es : set<Edge>)
   //reads e2o(es)
      reads set e <- es :: e.f
      reads set e <- es :: e.t
      requires edgesAreConsistentWithDafnyHeap(es)
    {
       var partition := partitionedIncomingEdges(es);

       forall p <- partition.Keys :: | (set e <- partition[p] | pred(e.m) :: e) | <= 1
    } 

    predicate ConstrainedModesIncomingEdges(pred : set<Mode> -> bool, es : set<Edge>)
   //reads e2o(es)
      reads set e <- es :: e.f
      reads set e <- es :: e.t
      requires edgesAreConsistentWithDafnyHeap(es)   
    {
       var partition := partitionedIncomingEdges(es);

       forall p <- partition.Keys ::  pred((set e <- partition[p] :: e.m))
    } 


//AKA Predicates is Monotonic / Covariant 
lemma ItsaTrickWithaSubset<T>(less : set<T>, more : set<T>, pred : T -> bool)
  requires less <= more
  ensures   (set e <- less) <= (set e <- more)
  ensures   (set e <- less | pred(e)) <= (set e <- more | pred(e))
{}


//either Owned or Loaned, never both
predicate OLD___OwnedOrLoanedIncoming(partition : Incoming) 
{
 (forall o <- partition.Keys :: 
      |(set e <- partition[o] | e.m.Owned? || e.m.Loaned? )| <= 1)
}

predicate OneOwnerIncoming(partition : Incoming)
 {
  (forall o <- partition.Keys :: 
      (exists e <- partition[o] :: e.m.Owned?) ==> (
         // ((|partition[o]|) <= 1) 
         GroundSingleton( partition[o] )  ))
           //if there's an Owner, it should be the *only* reference (could be XU but isn't...)
 }

predicate BorrowedNotOwnedIncoming(partition : Incoming)
 {
  (forall o <- partition.Keys :: 
      //  var modes := set pes <- partition[o] :: pes.m;
      (exists e <- partition[o] :: e.m.Borrow?) ==> 
          (forall e <- partition[o] :: not(e.m.Owned?))) 
           //if there's a Borrow, there can't be an Owned reference}
 }

predicate BorrowsLoansConsistentPermissionIncoming(partition : Incoming) 
     { (forall o <- partition.Keys, e <- partition[o],  e' <- partition[o] 
        | (e.m.Borrow? || e.m.Loaned?) && (e'.m.Borrow? || e'.m.Loaned?)
        :: e.m.perm == e'.m.perm)}
          // all Borrows and Loans must have the same permission.
          
predicate OLD__OnlyOneWriterIncoming(partition : Incoming) 
     { (forall o <- partition.Keys :: 
        |(set e <- partition[o] | (e.m.Borrow? && e.m.perm == Write) :: e )| <= 1)}
          //if there's a write borrow it must be the only one.


predicate  WriterEdge(e : Edge) { e.m.Borrow? && e.m.perm == Write }

predicate  OwnedOrLoanedEdge(e : Edge) { e.m.Owned? || e.m.Loaned? }


predicate  OwnedOrLoanedEdgeIncoming(partition : Incoming) 
     { (forall o <- partition.Keys :: 
        |(set e <- partition[o] | OwnedOrLoanedEdge(e) )| <= 1)}
          //if there's a write borrow it must be the only one.
          
predicate  OnlyOneWriterEdgeIncoming(partition : Incoming) 
     { (forall o <- partition.Keys :: 
        |(set e <- partition[o] | WriterEdge(e) )| <= 1)}
          //if there's a write borrow it must be the only one.

predicate  OnlyOnePredEdges(pred : Edge -> bool, es : set<Edge>  ) 
     { |FilteredEdges(pred, es)| <= 1}

lemma OnlyOnePredEdgesMonotonic(pred : Edge -> bool, less : set<Edge>, more : set<Edge> ) 
  requires less <= more
  ensures OnlyOnePredEdges(pred, less) <== OnlyOnePredEdges(pred, more)
  {
     FilteredEdgesMonotonic(pred, less, more);
     FewerIsLess(FilteredEdges(pred, less),FilteredEdges(pred, more));
     assert |FilteredEdges(pred, less)|    <=    |FilteredEdges(pred, more)|;
     assert (|FilteredEdges(pred, less)|  <= 1)  <== (| FilteredEdges(pred, more) | <= 1);
     assert OnlyOnePredEdges(pred, less) <== OnlyOnePredEdges(pred, more);

}

function  FilteredEdges(pred : Edge -> bool, es : set<Edge>) : (r : set<Edge>) 
   ensures r <= es
{
  set e <- es | pred(e) :: e
}

lemma FilteredEdgesMonotonic(pred : Edge -> bool, less : set<Edge>, more : set<Edge> ) 
  requires less <= more
  ensures FilteredEdges(pred, less)    <=     FilteredEdges(pred, more)
  ensures |FilteredEdges(pred, less)|  <=    |FilteredEdges(pred, more)|
{
  FewerIsLess(FilteredEdges(pred, less),FilteredEdges(pred, more));
}

predicate OnlyOnePredIncoming(pred : Edge -> bool, partition : map<Object,set<Edge>>) 
     { forall o <- partition.Keys ::  OnlyOnePredEdges(pred, partition[o]) }


lemma OnlyOnePredIncomingMonotonic(pred : Edge -> bool, lesp : map<Object,set<Edge>>, morp : map<Object,set<Edge>>)
    requires partitionedLessEQ(lesp, morp) 
    ensures  OnlyOnePredIncoming(pred, lesp) <== OnlyOnePredIncoming(pred, morp)
    {
    forall l <- lesp.Keys
       ensures OnlyOnePredEdges(pred, lesp[l]) <== OnlyOnePredEdges(pred, morp[l])
     {
       OnlyOnePredEdgesMonotonic(pred, lesp[l], morp[l]);
       // FewerIsLess(lesp[l],morp[l]);
     }
    }  


predicate OnlyOneWriterIncoming(partition : map<Object,set<Edge>>) 
     { OnlyOnePredIncoming(WriterEdge, partition )}



predicate OnlyOneOwnedOrLoanedIncoming(partition : map<Object,set<Edge>>) 
     { OnlyOnePredIncoming(OwnedOrLoanedEdge, partition )}

lemma OnlyOneWriterIncomingMonotonic(lesp : map<Object,set<Edge>>, morp : map<Object,set<Edge>>)
    requires partitionedLessEQ(lesp, morp) 
    ensures  OnlyOneWriterIncoming(lesp) <== OnlyOneWriterIncoming(morp)
    {
      OnlyOnePredIncomingMonotonic(WriterEdge , lesp, morp);
       }
