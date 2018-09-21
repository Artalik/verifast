//@ #include <multiset.gh>

/*@

fixpoint bool option_le(option<int> x, int y) {
  switch (x) {
    case none: return true;
    case some(x0): return x0 <= y;
  }
}

fixpoint bool option_le_option(option<int> x, option<int> y) {
  switch (y) {
    case none: return true;
    case some(y0): return option_le(x, y0);
  }
}

fixpoint bool is_sorted_between(option<int> lower, mapping(int, int) vs, option<int> upper, int b, nat n) {
  switch (n) {
    case zero: return option_le_option(lower, upper);
    case succ(p):
      return option_le(lower, select(vs, b)) &&
             is_sorted_between(some(select(vs, b)), vs, upper, b+1, p);
  }
}

fixpoint bool le(int x, int y) { return x <= y; }
fixpoint bool ge(int x, int y) { return x >= y; }

@*/

int get (int *a, int i)
//@ requires mapping_model(a, ?b, ?e, ?start) &*& b <= i &*& i < e;
//@ ensures mapping_model(a, b, e, start) &*& result == select(start, i);
{
  //@ mapping_model_select_unfold(a, b, e, start, i);
  int ai = a[i];
  //@ mapping_model_select_fold(a, b, e, start, i);
  return ai;
}

void set (int* a, int i, int v)
//@ requires mapping_model(a, ?b, ?e, ?start) &*& b <= i &*& i < e;
//@ ensures mapping_model(a, b, e, store(start, i, v));
{
  //@ mapping_model_select_unfold(a, b, e, start, i);
  a[i] = v;
  //@ mapping_model_store_fold(a, b, e, start, i);
}

/*@

fixpoint mapping(int, int) mapping_swap(mapping(int, int) mp, int i, int j) {
  return store(store(mp, j, select(mp, i)), i, select(mp, j));
}

@*/

void swap (int *a, int i, int j)
//@ requires mapping_model(a, ?b, ?e, ?start) &*& b <= i &*& i < j &*& j < e;
//@ ensures mapping_model(a, b, e, mapping_swap(start, i, j));
{
  int aj = get(a, j);
  set(a, j, get(a, i));
  set(a, i, aj);
}

/*@

lemma void swap_invariant (int lo, int hi, int i, int j, int pivot, mapping(int, int) mp)
requires lo <= i &*& i < j &*& j <= hi &*& select(mp, j) <= pivot &*&
         mapping_forall(mp, (ge)(pivot), lo, nat_of_int(i-lo)) == true &*&
         mapping_forall(mp, (le)(pivot), i, nat_of_int(j-i)) == true;
ensures mapping_forall(mapping_swap(mp, i, j), (ge)(pivot), lo, nat_of_int(i-lo)) == true &*&
        mapping_forall(mapping_swap(mp, i, j), (le)(pivot), i+1, nat_of_int(j-i)) == true &*&
        mapping_multiset(lo, nat_of_int(hi+1 - lo), mapping_swap(mp, i, j)) == mapping_multiset(lo, nat_of_int(hi+1 - lo), mp);
{
  mapping_forall_store(mp, (ge)(pivot), lo, nat_of_int(i-lo), j, select(mp, i));
  mapping_forall_store(store(mp, j, select(mp, i)), (ge)(pivot), lo, nat_of_int(i-lo), i, select(mp, j));
  note (nat_of_int(j-i) == succ(nat_of_int(j-i-1)));
  mapping_forall_store(mp, (le)(pivot), i+1, nat_of_int(j-i-1), j, select(mp, i));
  mapping_forall_store(store(mp, j, select(mp, i)), (le)(pivot), i+1, nat_of_int(j-i-1), i, select(mp, j));
  int_diff_nat_of_int(i+1, j);
  mapping_forall_close_right(mapping_swap(mp, i, j), (le)(pivot), i+1, j, nat_of_int(j-i-1));
  int_diff_nat_of_int(lo, hi+1);
  mapping(int, nat) m1 = multiset_select_in(lo, hi+1, nat_of_int(hi+1-lo), mp, j);
  same_multiset_store_in(lo, hi+1, nat_of_int(hi+1-lo), mp, m1, j, select(mp, i));
  same_multiset_store_in(lo, hi+1, nat_of_int(hi+1-lo), store(mp, j, select(mp, i)), m1, i, select(mp, j));
}

@*/

int partition(int *a, int lo, int hi)
  //@ requires mapping_model(a, lo, hi+1, ?start) &*& lo <= hi;
  /*@
  ensures
      lo <= result &*& result <= hi &*& mapping_model(a, lo, hi+1, ?end) &*&
      mapping_forall(end, (ge)(select(end, result)), lo, nat_of_int(result-lo)) == true &*&
      mapping_forall(end, (le)(select(end, result)), result+1, nat_of_int(hi-result)) == true &*&
      mapping_multiset(lo, nat_of_int(hi+1 - lo), end) == mapping_multiset(lo, nat_of_int(hi+1 - lo), start);
  @*/
{
  int pivot = get(a, hi);
  int i = lo - 1;
  int j;
  //@ mapping(int, int) mp = start;
  for (j = lo; j < hi; j++)
    /*@
    invariant
      lo - 1 <= i &*& i < j &*& j <= hi &*& pivot == select(mp, hi) &*&
      mapping_model(a, lo, hi+1, mp) &*&
      mapping_forall(mp, (ge)(pivot), lo, nat_of_int(i+1-lo)) == true &*&
      mapping_forall(mp, (le)(pivot), i+1, nat_of_int(j-i-1)) == true &*&
      mapping_multiset(lo, nat_of_int(hi+1 - lo), mp) == mapping_multiset(lo, nat_of_int(hi+1 - lo), start);
    @*/
  {
    int aj = get(a, j);
    if (aj < pivot) {
      i++;
      if (i < j) {
        swap(a, i, j);
        //@ swap_invariant (lo, hi, i, j, pivot, mp);
        //@ mp = mapping_swap(mp, i, j);
      } else {
        //@ assert i == j;
      }
      //@ int_diff_nat_of_int(lo, i);
      //@ mapping_forall_close_right(mp, (ge)(pivot), lo, i, nat_of_int(i-lo));
    } else {
    //@ int_diff_nat_of_int(i+1, j);
    //@ mapping_forall_close_right(mp, (le)(pivot), i+1, j, nat_of_int(j-i-1));
    }
  }
  //@ assert j == hi;
  i++;
  if (i < hi) {
    swap(a, i, hi);
    //@ swap_invariant (lo, hi, i, hi, pivot, mp);
  }
  return i;
}

/*@
lemma void is_sorted_append(option<int> lower, mapping(int, int) vs, int pivot, int b, nat m, int p, nat n, int e)
requires is_sorted_between(lower, vs, some(pivot), b, m) == true &*& is_sorted_between(some(pivot), vs, none, p, n) == true &*&
             int_diff(b, p, m) == true &*& b <= p &*& int_diff(p, e, n) == true &*& p <= e;
ensures is_sorted_between(lower, vs, none, b, nat_of_int(e-b)) == true;
{
  switch (m) {
    case zero:
      switch (lower) { case none: case some(l): }
      int_diff_le(b, p, m);
      int_diff_le(p, e, n);
      switch(n) {case zero: case succ(pred): }
    case succ(pred):
      note (nat_of_int(e-b) == succ(nat_of_int(e-b-1)));
      is_sorted_append(some(select(vs, b)), vs, pivot, b+1, pred, p, n, e);
    }
}

lemma void is_sorted_outside(option<int> lower, mapping(int, int) a, option<int> upper, int b, int e, nat n, int i, int v)
requires is_sorted_between(lower, a, upper, b, n) == true &*& int_diff(b, e, n) == true &*& b <= e &*& (i < b || e <= i);
ensures is_sorted_between(lower, store(a, i, v), upper, b, n) == true;
{
  switch(n) {
    case zero:
    case succ(pred):
      is_sorted_outside(some(select(a, b)), a, upper, b+1, e, pred, i, v);
  }
}

lemma void same_multiset_forall(mapping(int, int) a1, mapping(int, int) a2, int b, nat n, int c, nat m, int e, fixpoint(int, bool) p)
requires mapping_multiset(b, n, a1) == mapping_multiset(b, n, a2) &*& mapping_forall(a1, p, b, n) == true &*& b <= c &*& c <= e &*&
         int_diff(b, e, n) == true &*& int_diff(c, e, m) == true;
ensures mapping_forall(a2, p, c, m) == true;
{
  switch(m) {
    case zero:
    case succ(pred):
      same_multiset_forall(a1, a2, b, n, c+1, pred, e, p);
      int_diff_le(b, e, n);
      close same_multiset(a2, a1, b, e);
      int i = same_multiset_assoc(a2, a1, b, e, c);
      mapping_forall_in(a1, p, b, e, n, i);
      open same_multiset(a2, a1, b, e);
  }
}

lemma void is_sorted_between_upper(option<int> lower, mapping(int, int) mp, int b, nat n, int bound)
requires is_sorted_between(lower, mp, none, b, n) == true &*& mapping_forall(mp, (ge)(bound), b, n) == true &*& option_le(lower, bound) == true;
ensures is_sorted_between(lower, mp, some(bound), b, n) == true;
{
  switch(n) {
    case zero:
    case succ(pred):
      is_sorted_between_upper(some(select(mp, b)), mp, b+1, pred, bound);
  }
}

lemma void is_sorted_between_lower(option<int> lower, mapping(int, int) mp, int b, nat n, int bound)
requires is_sorted_between(lower, mp, none, b, n) == true &*& mapping_forall(mp, (le)(bound), b, n) == true;
ensures is_sorted_between(some(bound), mp, none, b, n) == true;
{
  switch(n) {
    case zero:
    case succ(pred):
  }
}

lemma void is_sorted_same_mapping(option<int> lower, mapping(int, int) mp1, mapping(int, int) mp2, option<int> upper, int b, nat n)
requires is_sorted_between(lower, mp1, upper, b, n) == true &*& same_mapping(mp1, mp2, b, n) == true;
ensures is_sorted_between(lower, mp2, upper, b, n) == true;
{
  switch(n) {
    case zero:
    case succ(pred):
      is_sorted_same_mapping(some(select(mp1, b)), mp1, mp2, upper, b+1, pred);
  }
}
@*/

void quicksort(int *a, int lo, int hi)
  //@ requires mapping_model(a, lo, hi+1, ?start);
  /*@ ensures mapping_model(a, lo, hi+1, ?end) &*& mapping_multiset(lo, nat_of_int(hi+1-lo), end) == mapping_multiset(lo, nat_of_int(hi+1-lo), start) &*&
       lo <= hi+1 ? (is_sorted_between(none, end, none, lo, nat_of_int(hi+1-lo)) == true) : true; @*/
{
  if (lo > hi) {
    return;
  } else {
    int p = partition(a, lo, hi);
    //@ assert mapping_model(a, lo, hi+1, ?partitioned);
    //@ int pivot = select(partitioned, p);
    //@ mapping_model_select_unfold(a, lo, hi+1, partitioned, p);
    quicksort(a, lo, p-1);
    //@ assert mapping_model(a, lo, p, ?smalls);
    //@ int_diff_nat_of_int(lo, p);
    //@ same_multiset_forall(partitioned, smalls, lo, nat_of_int(p-lo), lo, nat_of_int(p-lo), p, (ge)(pivot));
    //@ is_sorted_between_upper(none, smalls, lo, nat_of_int(p-lo), pivot);
    quicksort(a, p+1, hi);
    //@ assert mapping_model(a, p+1, hi+1, ?bigs);
    //@ int_diff_nat_of_int(p+1, hi+1);
    //@ same_multiset_forall(partitioned, bigs, p+1, nat_of_int(hi-p), p+1, nat_of_int(hi-p), hi+1, (le)(pivot));
    //@ is_sorted_between_lower(none, bigs, p+1, nat_of_int(hi-p), pivot);
    //@ note(nat_of_int(hi+1-p) == succ(nat_of_int(hi-p)));
    //@ is_sorted_outside(some(pivot), bigs, none, p+1, hi+1, nat_of_int(hi-p), p, pivot);
    //@ mapping_model_out_of_range(a, p+1, hi+1, bigs, p, pivot);
    //@ same_multiset_store_out_left(p+1, hi+1, nat_of_int(hi-p), bigs, p, pivot);
    //@ open same_multiset(bigs, store(bigs, p, pivot), p+1, hi+1);
    //@ bigs = store(bigs, p, pivot);
    //@ close same_multiset(partitioned, bigs, p, hi+1);
    //@ close mapping_model(a, p, hi+1, bigs);
    //@ mapping(int, int) end = mapping_model_concat(a, smalls, bigs, lo, nat_of_int(p-lo), p, hi+1);
    //@ same_mapping_same_multiset(smalls, end, lo, nat_of_int(p-lo));
    //@ same_mapping_same_multiset(bigs, end, p, nat_of_int(hi+1-p));
    //@ close same_multiset(bigs, end, p, hi+1);
    //@ same_multiset_trans(partitioned, bigs, end, p, hi+1);
    //@ close same_multiset(partitioned, end, lo, p);
    //@ same_multiset_concat(partitioned, end, lo, p, hi+1);
    //@ open same_multiset(partitioned, end, lo, hi+1);
    //@ is_sorted_same_mapping(none, smalls, end, some(pivot), lo, nat_of_int(p-lo));
    //@ is_sorted_same_mapping(some(pivot), bigs, end, none, p, nat_of_int(hi+1-p));
    //@ is_sorted_append(none, end, select(end, p), lo, nat_of_int(p-lo), p, nat_of_int(hi+1-p), hi+1);
  }
}
