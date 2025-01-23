//Incoming depends on Edges

type Incoming = map<Object,set<Edge>>

function partitionedIncomingEdges(es : set<Edge>) : (r : map<Object,set<Edge>>)

  requires edgesAreConsistentWithDafnyHeap(es)
  reads set e <- es :: e.f
  reads set e <- es :: e.t

  ensures forall k <- r.Keys, e <- r[k] :: e in es && e.t == k
  ensures forall e <- es :: (e.t in r) && (e in r[e.t])
  ensures (set k <- r.Keys, e <- r[k] :: e) == es
  ensures forall k <- r.Keys :: r[k] == incomingEdges(k, es)
{
    var incomingPartions : set<Object> := set e <- es :: e.t;
    map o <- incomingPartions :: incomingEdges(o, es)
}



predicate {:opnly} partitionedLessEQ(lesp : Incoming, morp : Incoming)
{
   && lesp.Keys <= morp.Keys
   && (forall l <- lesp.Keys :: lesp[l]   <= morp[l])
   && (forall l <- lesp.Keys :: |lesp[l]| <= |morp[l]|)
}

lemma  partitionedIncomingEdgesMonotonic(
        less : set<Edge>, more : set<Edge>,
        lesp : map<Object,set<Edge>>, morp : map<Object,set<Edge>>)
   requires edgesAreConsistentWithDafnyHeap(less)
   requires edgesAreConsistentWithDafnyHeap(more)
   requires less <= more
   requires lesp == partitionedIncomingEdges(less)
   requires morp == partitionedIncomingEdges(more)

   ensures lesp.Keys <= morp.Keys
   ensures forall l <- lesp.Keys :: lesp[l]   <= morp[l]
   ensures forall l <- lesp.Keys :: |lesp[l]| <= |morp[l]|

   ensures partitionedLessEQ(lesp, morp)
{
  forall l <- lesp.Keys
     ensures |lesp[l]| <= |morp[l]|
     {
        FewerIsLess(lesp[l],morp[l]);
     }

}


predicate uniqueIncoming( o : Object, osgp : Incoming)
{
  (o in osgp) && (|osgp[o]| == 1)
}





lemma IncomingEdgesAreIncoming(es : set<Edge>, ins : Incoming )
   requires edgesAreConsistentWithDafnyHeap(es)
   requires ins == partitionedIncomingEdges(es)
   ensures  forall e <- es :: e in ins[e.t]
   ensures  (set ines <- ins.Values, e <- ines :: e) == es
   ensures  forall o <- ins.Keys :: ins[o] == incomingEdges(o,es)
{
  // assert ObjectsToEdges(os,es);
  // assert ObjectsToIncoming(os,ins);
}




lemma {:timeLimit 30} {:isolate_assertions} FewerPartitionedIncomingEdgesValid(
        less : set<Edge>, more : set<Edge>,
        lesp : Incoming, morp : Incoming)
    requires less <= more
    requires lesp == partitionedIncomingEdges(less)
    requires morp == partitionedIncomingEdges(more)

    requires edgesAreConsistentWithDafnyHeap(less)
    requires edgesAreConsistentWithDafnyHeap(more)

    requires OnlyOneOwnedOrLoanedIncoming(morp)
    requires OneOwnerIncoming(morp)
    requires BorrowedNotOwnedIncoming(morp)
    requires BorrowsLoansConsistentPermissionIncoming(morp)
    requires OnlyOneWriterIncoming(morp)

    requires IncomingReferencesConstraintsOK(more)

    ensures OnlyOneOwnedOrLoanedIncoming(lesp)
    ensures OneOwnerIncoming(lesp)
    ensures BorrowedNotOwnedIncoming(lesp)
    ensures BorrowsLoansConsistentPermissionIncoming(lesp)
    ensures OnlyOneWriterIncoming(lesp)

   {
    partitionedIncomingEdgesMonotonic(less, more, lesp, morp);
    OnlyOnePredIncomingMonotonic(WriterEdge , lesp, morp);
    OnlyOnePredIncomingMonotonic(OwnedOrLoanedEdge , lesp, morp);

   }//end FewerPartitionedIncomingEdgesValid


function partitionUnion(m: Incoming, m': Incoming): (r: Incoming)
    ensures r.Keys == m.Keys + m'.Keys
    ensures forall x <- m  :: r[x] >=  m[x]
    ensures forall x <- m' :: r[x] >= m'[x]
  {
     map x <- (m.Keys + m'.Keys) ::
       x := (if (x in m.Keys) then m[x] else {}) + (if (x in m'.Keys) then m'[x] else {})
  }




function IncomingReadSet(ins : Incoming) : set<Object>
{
  set es : set<Edge> <- ins.Values, e : Edge <- es,
    o : Object <- ({e.f} + {e.t}) :: o
}


predicate ObjectsToIncoming(os : set<Object>, ins : Incoming)
//  requires IncomingReadSet(ins) <= o
  //reads (set es <- ins.Values, e <- es, o <- {e.f}:: o)`fields
  reads (set es <- ins.Values, e <- es :: e.f)`fields
  //reads os`fields
  reads os + (set o <- os, v <- o.ValidReadSet() :: v)
  reads (set o <- os, v <- o.fields.Values :: v)
  reads ins.Keys + IncomingReadSet(ins)
  reads IncomingReadSet(ins)`fields
  requires forall o <- os :: o.Ready() && o.Valid() //DO I want this or not? or a separate lemma
{
  && (forall o <- os :: o.AllFieldsAreDeclared())
  && (forall es <- ins.Values, e <- es :: e.n in e.f.fields && e.f.fields[e.n] == e.t)
  && ((os == {}) ==> ((IncomingReadSet(ins)) + ins.Keys) == {})   //but not the other way cos of solitary nodes (incoming & outgoing = 0)
  && (var es := edges(os); forall e <- es :: (e.t in ins.Keys && e in ins[e.t]))
  && (forall o <- os, n <- o.fields.Keys ::  o.fields[n] in ins.Keys && edge(o,n) in ins[o.fields[n]])
  && (forall es <- ins.Values, e <- es :: (e.f in os) && (e.n in e.f.fields) && (e.m == e.f.fieldModes[e.n]) && (e.t == e.f.fields[e.n]))
}
//note that this doesn't require e.t to be in os, i.e. we don't require os is "ClosedHeap"
//or whatever we call it.
//perhaps we need more invairants or something to handle that case. grrr.
//how much should be explicit!!! how much implicit??


lemma {:timeLimit 120}
  ObjectsToIncomingLemma(os : set<Object>, ins : Incoming)
    requires forall o <- os :: o.Ready() && o.Valid()
    requires edgesAreConsistentWithDafnyHeap(edges(os))
    requires ins == partitionedIncomingEdges(edges(os))
    ensures  ObjectsToIncoming(os,ins)
{
  assert (forall es <- ins.Values, e <- es :: e.n in e.f.fields && e.f.fields[e.n] == e.t);
  assert ((os == {}) ==> ((IncomingReadSet(ins)) + ins.Keys) == {});  //but not the other way cos of solitary nodes (incoming & outgoing = 0)
  assert (var es := edges(os); forall e <- es :: (e.t in ins.Keys && e in ins[e.t]));
  //assert (forall o <- os, n <- o.fields.Keys :: o.fields[n] in ins.Keys); //HERE
  assert (forall o <- os, n <- o.fields.Keys :: edge(o,n) in ins[o.fields[n]]);
  assert (forall es <- ins.Values, e <- es :: (e.f in os) && (e.n in e.f.fields) && (e.m == e.f.fieldModes[e.n]) && (e.t == e.f.fields[e.n]));


  assert ObjectsToIncoming(os,ins);
}
