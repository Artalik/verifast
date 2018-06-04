//@ #include "vfarray.gh"

//@ #include "multiset.gh"

/*@
  
fixpoint array(int, int) array_swap(array(int, int) start, int i, int j) {
  return store(store(start, j, select(start, i)), i, select(start, j));
}
  

lemma void same_multiset_swap_in(array(int, int) start, int i, int j, int b, int e)
  requires b <= i &*& i < j &*& j < e;
  ensures same_multiset(start, array_swap(start, i, j), b, e);
{
   nat n = int_diff_always(b, e);
   int_diff_le(b, e, n);
   multiset<int> m = array_multiset(b, n, start);
   multiset<int> m2 = multiset_select_in(b, e, n, start, j);
   assert m == multiset_add(m2, select(start, j));
   same_multiset_store_in(b, e, n, start, m2, j, select(start, i));
   array(int, int) middle = store(start, j, select(start, i));
   assert array_multiset(b, n, middle) == multiset_add(m2, select(start, i));
   same_multiset_store_in(b, e, n, middle, m2, i, select(start, j));
   close same_multiset(start, array_swap(start, i, j), b, e);
}

lemma void same_multiset_swap_out_right(array(int, int) start, int i, int j, int b, int e)
  requires b <= e &*& e <= i &*& e <= j;
  ensures same_multiset(start, array_swap(start, i, j), b, e);
{
  nat n = int_diff_always(b, e);
  same_multiset_store_out_right(b, e, n, start, i, select(start, j));
  same_multiset_store_out_right(b, e, n, store(start, i, select(start, j)), j, select(start, i));
  same_multiset_trans(start, store(start, i, select(start, j)), array_swap(start, i, j), b, e);
}

@*/

int select_c(int* arr, int key)
//@ requires array_model(arr, ?lo, ?hi, ?m) &*& lo <= key &*& key < hi;
//@ ensures array_model(arr, lo, hi, m) &*& select(m, key) == result;
{
      //@ array_model_select_unfold(arr,lo,hi,m,key);
      int res = *(arr+key);
      //@ array_model_select_fold(arr,lo,hi,m,key);
      return res;
}

void update(int* arr, int key, int val)
//@ requires array_model(arr, ?lo, ?hi, ?m) &*& lo <= key &*& key < hi;
//@ ensures array_model(arr, lo, hi, store(m, key, val));
{
      //@ array_model_select_unfold(arr,lo,hi,m,key);
      *(arr+key) = val;
      //@ array_model_store_fold(arr,lo,hi,m,key);
}


void swap (int* a, int i, int j)
//@ requires array_model(a, ?b, ?e, ?start) &*& b <= i &*& i < j &*& j < e;
//@ ensures array_model(a, b, e, array_swap(start, i, j));
{
  int aj = select_c(a, j);
  update(a, j, select_c(a, i));
  update(a, i, aj);
}

/*@

    fixpoint bool geq(int a, int b) { return a >= b; }
    predicate minore(array(int, int) arr, int lo, nat n, int bound) =
      finite_multiset((geq)(bound), array_multiset(lo, n, arr), n);

    fixpoint bool leq(int a, int b) { return a <= b; }
    predicate majore(array(int,int) arr, int lo, nat n, int bound) =
      finite_multiset((leq)(bound), array_multiset(lo, n, arr), n);

    lemma void bound_empty_minore(array(int,int) arr, int lo, int bound)
      requires true;
      ensures minore(arr,lo,zero,bound);
      {
        finite_empty_multiset((geq)(bound));
        close minore(arr,lo,zero,bound);
      }

    lemma void bound_empty_majore(array(int,int) arr, int lo, int bound)
      requires true;
      ensures majore(arr,lo,zero,bound);
      {
         finite_empty_multiset((leq)(bound));
         close majore(arr,lo,zero,bound);
      }

    lemma void clear_minore(array(int, int) a, int lo, nat n, int bound)
    requires minore(a, lo, n, bound);
    ensures true;
    {
      open minore(a, lo, n, bound);
      finite_multiset_clear((geq)(bound), array_multiset(lo, n, a), n);
    }

    lemma void clear_majore(array(int, int) a, int lo, nat n, int bound)
    requires majore(a, lo, n, bound);
    ensures true;
    {
      open majore(a, lo, n, bound);
      finite_multiset_clear((leq)(bound), array_multiset(lo, n, a), n);
    }

    lemma void dup_majore(array(int, int) arr, int b, nat n, int bound)
    requires majore(arr, b, n, bound);
    ensures majore(arr, b, n, bound) &*& majore(arr, b, n, bound);
    {
      open majore(arr, b, n, bound);
      finite_multiset_dup((leq)(bound), array_multiset(b, n, arr), n);
      close majore(arr, b, n, bound);
      close majore(arr, b, n, bound);
    }

    lemma void one_more_bound_minore(array(int,int) arr, int lo, nat n, int hi, int bound)
    	requires minore(arr,lo,n,bound) &*& int_diff(lo, hi, n) == true &*& lo <= hi &*& select(arr,hi) < bound;
    	ensures minore(arr,lo,succ(n),bound);
    	{
    	   open minore(arr, lo, n, bound);
    	   array_multiset_right(arr, lo, hi, n);
    	   finite_multiset_add((geq)(bound), array_multiset(lo, n, arr), select(arr, hi));
    	   close minore(arr, lo, succ(n), bound);
    	}
    	
    lemma void one_more_bound_majore(array(int,int) arr, int lo, nat n, int hi, int bound)
    	requires majore(arr,lo,n,bound) &*& int_diff(lo, hi, n) == true &*& lo <= hi &*& select(arr,hi) >= bound;
    	ensures majore(arr,lo,succ(n),bound);
    	{
    	   open majore(arr, lo, n, bound);
    	   array_multiset_right(arr, lo, hi, n);
    	   finite_multiset_add((leq)(bound), array_multiset(lo, n, arr), select(arr, hi));
    	   close majore(arr, lo, succ(n), bound);
        }
     
    lemma void one_more_bot_bound_majore(array(int,int) arr, int lo, int hi, int bound, nat length)
    	requires majore(arr,lo,length,bound) &*& select(arr,hi) < bound &*& lo < hi &*& int_diff(lo, hi, length) == true;
    	ensures majore(array_swap(arr,lo,hi),lo+1,length,bound);
    	{
    	  multiset<int> m = array_multiset(lo, length, arr);
          array_multiset_right(arr, lo, hi, length);
    	  assert array_multiset(lo, succ(length), arr) == multiset_add(m, select(arr, hi));
          same_multiset_swap_in(arr,lo,hi,lo,hi+1);
          open same_multiset(arr, array_swap(arr, lo, hi), lo, hi+1);
          int_diff_le(lo, hi, length);
    	  assert array_multiset(lo, succ(length), array_swap(arr,lo,hi)) == multiset_add(m, select(arr, hi));
    	  regular_multiset_add(array_multiset(lo+1, length, array_swap(arr, lo, hi)), m, select(arr, hi)); 
    	  assert array_multiset(lo+1, length, array_swap(arr,lo,hi)) == m;
    	  open majore(arr, lo, length, bound);
    	  close majore(array_swap(arr, lo, hi), lo+1, length, bound);
    	}

    lemma void minore_out_length(array(int,int) arr,int lo, int hi, int bound, int i, int j, nat length)
	requires minore(arr,lo,length,bound) &*& hi <= i &*& hi <= j &*& int_diff(lo, hi, length) == true &*& lo <= hi;
    	ensures minore(array_swap(arr,i,j),lo,length,bound);
    	{
    	  same_multiset_swap_out_right(arr, i, j, lo, hi);
    	  open same_multiset(arr, array_swap(arr, i, j), lo, hi);
    	  int_diff_le(lo, hi, length);
    	  open minore(arr, lo, length, bound);
    	  close minore(array_swap(arr, i, j), lo, length, bound);
    	}

    lemma void minore_out(array(int,int) arr,int lo, int hi, nat n, int bound, int i, int j)
    	requires minore(arr,lo,n,bound) &*& int_diff(lo, hi, n) == true &*& lo <= hi &*& hi <= i &*& hi <= j;
    	ensures minore(array_swap(arr,i,j),lo,n,bound);
    	{
    	  minore_out_length(arr, lo, hi, bound, i, j, n);
    	}

    lemma void majore_out(array(int,int) arr,int lo, int bound)
    	requires majore(arr,lo,zero,bound);
    	ensures majore(arr,lo+1,zero,bound);
    	{
    	   clear_majore(arr,lo,zero,bound);
    	   bound_empty_majore(arr, lo+1, bound);
        }

    lemma void majore_bot_less(array(int,int) arr,int lo, nat n, int bound)
    	requires majore(arr,lo,succ(n),bound);
    	ensures majore(arr,lo+1,n,bound);
    	{
           open majore(arr,lo,succ(n),bound);
           finite_multiset_remove((leq)(bound), array_multiset(lo+1, n, arr), select(arr, lo), n);
           close majore(arr,lo+1,n,bound);
    	}
    
    lemma void majore_top_more(array(int,int) arr,int lo,int hi,nat n,int bound)
    	requires majore(arr,lo,n,bound) &*& int_diff(lo, hi, n) == true &*& lo <= hi &*& select(arr,hi) >= bound;
    	ensures majore(arr,lo,succ(n),bound);
    	{
    	   open majore(arr, lo, n, bound);
    	   array_multiset_right(arr, lo, hi, n);
    	   finite_multiset_add((leq)(bound), array_multiset(lo, n, arr), select(arr, hi));
    	   close majore(arr, lo, succ(n), bound);
    }
    
    lemma void swap_majore(array(int,int) arr,int lo, int hi, nat n, int bound, int i, int j)
    	requires majore(arr,lo,n,bound) &*& lo <= i &*& j < hi &*& i < j &*& int_diff(lo, hi, n) == true;
    	ensures majore(array_swap(arr,i,j),lo,n,bound);
    	{
    	  open majore(arr, lo, n, bound);
    	  same_multiset_swap_in(arr, i, j, lo, hi);
    	  open same_multiset(arr, array_swap(arr, i, j), lo, hi);
    	  int_diff_le(lo, hi, n);
    	  close majore(array_swap(arr, i, j), lo, n, bound);
    	}
@*/

int partition (int* a, int lo, int hi)
//@ requires array_model(a, lo, hi, ?start) &*& lo <= hi &*& *(a+hi) |-> ?p &*& p == select(start, hi);
/*@ ensures array_model(a, lo, hi+1, ?end) &*& same_multiset(start, end, lo, hi+1) &*&
      lo <= result &*& result <= hi &*&
      select(end, result) == p &*&
      minore(end, lo, nat_of_int(result-lo), select(end,result)) &*&
      majore(end, result+1, nat_of_int(hi-result), select(end,result)); @*/
{
  int pivot = *(a+hi);
  int i = lo - 1;
  int j;
  //@ same_multiset_refl(start, lo, hi);
  //@ bound_empty_minore(start,lo,p);
  //@ nat left_length = zero;
  //@ nat middle_length = zero;
  //@ bound_empty_majore(start,i+1,p);
  for (j = lo; j < hi; j++) 
  /*@ invariant array_model(a,lo,hi,?arr) &*& lo <= j &*& j < hi+1 &*& i < j &*& int_diff(i+1, j, middle_length) == true &*& lo -1 <= i &*& same_multiset(start, arr, lo, hi) &*& select(arr, hi) == p
      &*& minore(arr,lo,left_length,p) &*& int_diff(lo, i+1, left_length) == true &*& majore(arr,i+1,middle_length,p); @*/
  { 
    int aj = select_c(a, j);
    if (aj < pivot) {
      i++;
      if (i < j) {
        swap(a, i, j);
        //@ same_multiset_swap_in(arr, i, j, lo, hi);
        //@ same_multiset_trans(start, arr, array_swap(arr, i, j), lo, hi);
    	//@ minore_out(arr,lo, i, left_length, p, i, j);
      	//@ one_more_bound_minore(array_swap(arr,i,j),lo,left_length,i,p);
      	//@ one_more_bot_bound_majore(arr, i, j, p, middle_length);
      }else{
        //@ switch(middle_length) {case zero: case succ(pred): assert false;}
      	//@ one_more_bound_minore(arr,lo,left_length,i,p);
      	//@ majore_out(arr, i, p);
      }
      //@ int_diff_translate(lo, i, 1, left_length);
      //@ int_diff_translate(i, j, 1, middle_length);
      //@ left_length = succ(left_length);
    }else{
   	//@ one_more_bound_majore(arr, i+1, middle_length, j, p);
   	//@ middle_length = succ(middle_length);
        //@ int_diff_translate(i, j, 1, middle_length);
    }
    
  }
  //@ assert array_model(a, lo, hi, ?arr);
  //@ nat right_length = int_diff_always(i+1, hi);
  //@ assert j == hi;
  //@ majore_top_more(arr, i+1, hi, middle_length, p);
  i++;
  //@ empty_array(a, hi+1, arr);
 //@ array_model_select_fold(a, lo, hi+1, arr, hi);
 //@ same_multiset_add_at_end(start, arr, lo, hi);
  if (i < hi) {
    swap(a, i, hi);
  //@ same_multiset_swap_in(arr, i, hi, lo, hi+1);
  //@ same_multiset_trans(start, arr, array_swap(arr, i, hi), lo, hi+1);
  //@ minore_out(arr, lo, i, left_length, p, i, hi);
  //@ int_diff_translate(i,hi,1,middle_length);
  //@ swap_majore(arr, i, hi+1, succ(middle_length), p, i,hi);
  //@ majore_bot_less(array_swap(arr,i,hi), i, middle_length, p);
  //@ int_diff_le(i, hi, middle_length);
  }else{
  //@ majore_bot_less(arr, i, middle_length, p);
  //@ int_diff_le(i, hi, middle_length);
  }
  //@ int_diff_le(lo, i, left_length);
  return i;
}

/*@ predicate sorted_nat(array(int,int) arr, int b, nat n) =
      n == zero ? true :
        (n == succ(zero) ? true :
           select(arr, b) <= select(arr, b+1) &*& sorted_nat(arr, b+1, ?p) &*& n == succ(p));

    predicate sorted(array(int,int) arr, int b, int e) =
      b <= e ? sorted_nat(arr, b, nat_of_int(e-b)) : true;
    
    lemma void empty_sorted(array(int,int)arr, int b, int e)
    	requires b >= e;
    	ensures sorted(arr, b, e);
    	{
    	  if (b == e) {
    	    close sorted_nat(arr, b, zero);
    	    close sorted(arr, b, e);
    	  } else {
    	    close sorted(arr, b, e);
    	  }
    	}
    	
/*    lemma void ensure_empty_array(int*a, int b,array(int,int) arr)
    	requires array_model(a,b,b,arr);
    	ensures true;
    	{open array_model(a,b,b,arr);} */
    	
    lemma void same_multi_etend(array(int,int) end, array(int,int) end1, int b, int e)
    	requires same_multiset(end,end1,b,e) &*& b <= e;
    	ensures same_multiset(end,store(end1,b-1, select(end,b-1)),b-1,e);
    	{
    	   nat n = int_diff_always(b, e);
    	   int_diff_le(b, e, n);
    	   same_multiset_store_out_left(b, e, n, end1, b-1, select(end, b-1));
    	   same_multiset_trans(end, end1, store(end1, b-1, select(end, b-1)), b, e);
    	   close_same_multiset(end, store(end1, b-1, select(end, b-1)), b, e);
    	}
    	
    lemma void sorted_etend(array(int,int) end, int b, nat n, int p, int v)
    	requires sorted_nat(end, b, n) &*& p < b;
    	ensures sorted_nat(store(end, p, v), b, n);
    	{
    	  switch(n) {
    	    case zero: {
    	      open sorted_nat(end, b, zero);
    	      close sorted_nat(store(end, p, v), b, zero);
    	    }
    	    case succ(pred): {
    	      switch(pred) {
    	        case zero: {
    	          open sorted_nat(end, b, succ(zero));
    	          close sorted_nat(store(end, p, v), b, succ(zero));
    	        }
    	        case succ(ppred): {
                  open sorted_nat(end, b, succ(pred));
    	          sorted_etend(end, b+1, pred, p, v);
    	          close sorted_nat(store(end, p, v), b, n);
    	        }
    	      }
    	    }
    	  }
    	}
    	
    lemma void sorted_destruct(array(int, int) arr, int b, nat n)
    requires sorted_nat(arr, b, succ(n));
    ensures sorted_nat(arr, b+1, n);
    {
      switch(n) {
        case zero: {
          open sorted_nat(arr, b, succ(n));
          close sorted_nat(arr, b+1, n);
        }
        case succ(pred): {
          open sorted_nat(arr, b, succ(n));
        }
      }
    }

    lemma void majore_weaken(array(int, int) arr, int b, nat n, int bound1, int bound2)
    requires majore(arr, b, n, bound1) &*& bound1 >= bound2;
    ensures majore(arr, b, n, bound2);
    {
      switch(n) {
        case zero: {
          clear_majore(arr, b, n, bound1);
          bound_empty_majore(arr, b, bound2);
        }
        case succ(p): {
          open majore(arr, b, n, bound1);
          finite_multiset_remove((leq)(bound1), array_multiset(b+1, p, arr), select(arr, b), p);
          close majore(arr, b+1, p, bound1);
          majore_weaken(arr, b+1, p, bound1, bound2);
          open majore(arr, b+1, p, bound2);
          finite_multiset_add((leq)(bound2), array_multiset(b+1, p, arr), select(arr, b));
          close majore(arr, b, n, bound2);
        }
      }
    }

    lemma void sorted_imp_majore(array(int, int) arr, int b, nat n)
    requires sorted_nat(arr, b, succ(n));
    ensures sorted_nat(arr, b+1, n) &*& majore(arr, b+1, n, select(arr, b));
    {
      switch(n) {
        case zero: {
          open sorted_nat(arr, b, succ(zero));
          close sorted_nat(arr, b+1, zero);
          bound_empty_majore(arr, b+1, select(arr, b));
        }
        case succ(p): {
          open sorted_nat(arr, b, succ(succ(p)));
          sorted_imp_majore(arr, b+1, p);
          assert select(arr, b) <= select(arr, b+1);
          if (p != zero && select(arr, b+1) > select(arr, b+2)) {
            switch(p) { case zero: assert false; case succ(pred): {
              open majore(arr, b+2, p, select(arr, b+1));
              finite_multiset_remove((leq)(select(arr, b+1)), array_multiset(b+3, pred, arr), select(arr, b+2), pred);
              assert false;
            }}
          }
          majore_weaken(arr, b+2, p, select(arr, b+1), select(arr, b));
          open majore(arr, b+2, p, select(arr, b));
          finite_multiset_add((leq)(select(arr, b)), array_multiset(b+2, p, arr), select(arr, b+1));
          close majore(arr, b+1, n, select(arr, b));
          switch(p) {
            case zero: {
              open sorted_nat(arr, b+2, zero);
              close sorted_nat(arr, b+1, succ(zero));
            }
            case succ(pred): {
              close sorted_nat(arr, b+1, n);
              assert true;
            }
          }
        }
      }
    }

    lemma void sorted_majore(array(int, int) arr, int b, nat n)
    requires sorted_nat(arr, b+1, n) &*& majore(arr, b+1, n, select(arr, b));
    ensures sorted_nat(arr, b, succ(n));
    {
      switch(n) {
        case zero: {
          open sorted_nat(arr, b+1, n);
          clear_majore(arr, b+1, n, select(arr, b));
          close sorted_nat(arr, b, succ(n));
        }
        case succ(p): {
              open majore(arr, b+1, n, select(arr, b));
              finite_multiset_remove((leq)(select(arr, b)), array_multiset(b+2, p, arr), select(arr, b+1), p);
              finite_multiset_clear((leq)(select(arr, b)), array_multiset(b+2, p, arr), p);
              close sorted_nat(arr, b, succ(n));
        }
      }
    }

    fixpoint array(int,int) concat_array(array(int, int) a0, array(int, int) a1, int b0, int e0, int e1, nat left) {
      switch (left) {
        case zero: return a1;
        case succ(p): return store(concat_array(a0, a1, b0+1, e0, e1, p), b0, select(a0, b0));
      }
    }

    lemma void concat_array_model(int* a, array(int, int) a0, array(int, int) a1, int b0, int e0, int e1, nat left)
    requires array_model(a, b0, e0, a0) &*& array_model(a, e0, e1, a1) &*& b0 <= e0 &*& e0 <= e1 &*& int_diff(b0, e0, left) == true;
    ensures array_model(a, b0, e1, concat_array(a0, a1, b0, e0, e1, left));
    {
      switch(left) {
        case zero: {
          assert b0 == e0;
          open array_model(a, b0, e0, a0);
        }
        case succ(p): {
          open array_model(a, b0, e0, a0);
          concat_array_model(a, a0, a1, b0+1, e0, e1, p);
          close array_model(a, b0, b0, concat_array(a0, a1, b0+1, e0, e1, p));
          array_model_store_fold(a, b0, e1, concat_array(a0, a1, b0+1, e0, e1, p), b0);
          assert array_model(a, b0, e1, concat_array(a0, a1, b0, e0, e1, left)); 
        }
      }
    }

    lemma void concat_array_same_multiset_left(array(int, int) a0, array(int, int) a1, int b0, int e0, int e1, nat left)
    requires b0 <= e0 &*& e0 <= e1 &*& int_diff(b0, e0, left) == true;
    ensures same_multiset(a0, concat_array(a0, a1, b0, e0, e1, left), b0, e0);
    {
      switch(left) {
        case zero: {
          close same_multiset(a0, concat_array(a0, a1, b0, e0, e1, zero), b0, e0);
        }
        case succ(p): {
          concat_array_same_multiset_left(a0, a1, b0+1, e0, e1, p);
          same_multiset_store_out_left(b0+1, e0, p, concat_array(a0, a1, b0+1, e0, e1, p), b0, select(a0, b0));
          same_multiset_trans(a0, concat_array(a0, a1, b0+1, e0, e1, p), concat_array(a0, a1, b0, e0, e1, left), b0+1, e0);
          close_same_multiset(a0, concat_array(a0, a1, b0, e0, e1, left), b0+1, e0);
        }
      }
    }

    lemma void concat_array_same_multiset_right(array(int, int) a0, array(int, int) a1, int b0, int e0, int e1, nat left)
    requires b0 <= e0 &*& e0 <= e1 &*& int_diff(b0, e0, left) == true;
    ensures same_multiset(a1, concat_array(a0, a1, b0, e0, e1, left), e0, e1);
    {
      switch(left) {
        case zero: {
          same_multiset_refl(a1, e0, e1);
        }
        case succ(p): {
          concat_array_same_multiset_right(a0, a1, b0+1, e0, e1, p);
          nat right = int_diff_always(e0, e1);
          same_multiset_store_out_left(e0, e1, right, concat_array(a0, a1, b0+1, e0, e1, p), b0, select(a0, b0));
          same_multiset_trans(a1, concat_array(a0, a1, b0+1, e0, e1, p), concat_array(a0, a1, b0, e0, e1, left), e0, e1);
        }
      }
    }

    lemma void concat_array_sorted(array(int,int) a0, array(int,int) a1, int b, int e0, int e1, nat left, nat right)
    requires sorted(a0, b, e0) &*& sorted(a1, e0, e1) &*& b <= e0 &*& e0 < e1 &*& int_diff(b, e0, left) == true &*& int_diff(e0+1, e1, right) == true &*&
    	     minore(a0, b, left, select(a1, e0)) &*& majore(a1, e0+1, right, select(a1, e0));
    ensures sorted(concat_array(a0, a1, b, e0, e1, left), b, e1);
    {
      switch (left) {
        case zero: {
          open sorted(a0, b, e0);
          open sorted_nat(a0, b, zero);
          clear_minore(a0, b, zero, select(a1, e0));
          clear_majore(a1, e0+1, right, select(a1, e0));
        }
        case succ(p): {
          switch(p) {
            case zero: {
              open sorted(a0, b, e0);
              open sorted_nat(a0, b, succ(zero));
              open minore(a0, b, succ(zero), select(a1, e0));
              finite_multiset_remove((geq)(select(a1, e0)), empty_multiset(), select(a0, b), zero);
              assert select(a0, b) <= select(a1, e0);
              open sorted(a1, e0, e1);
              int_diff_le(e0+1, e1, right);
              sorted_etend(a1, e0, succ(right), b, select(a0, b));
              close sorted_nat(concat_array(a0, a1, b, e0, e1, left), b, succ(succ(right)));
              close sorted(concat_array(a0, a1, b, e0, e1, left), b, e1);
              close minore(a0, b+1, zero, select(a1, e0));
              clear_minore(a0, b+1, zero, select(a1, e0));
              clear_majore(a1, e0+1, right, select(a1, e0));
            }
            case succ(pred): {
              open sorted(a0, b, e0);
              int_diff_le(b, e0, left);
              open sorted_nat(a0, b, succ(succ(pred)));
              int_diff_le(b+1, e0, p);
              close sorted(a0, b+1, e0);
              assert select(a0, b) <= select(a0, b+1);
              open minore(a0, b, left, select(a1, e0));
              finite_multiset_remove((geq)(select(a1, e0)), array_multiset(b+1, p, a0), select(a0, b), p);
              assert select(a0, b) <= select(a1, e0);
              close minore(a0, b+1, p, select(a1, e0));
              concat_array_sorted(a0, a1, b+1, e0, e1, p, right);
              nat leftright = int_diff_always(b+1, e1);
              int_diff_le(b+1, e1, leftright);
              open sorted(concat_array(a0, a1, b+1, e0, e1, p), b+1, e1);
              sorted_etend(concat_array(a0, a1, b+1, e0, e1, p), b+1, leftright, b, select(a0, b));
              close sorted_nat(concat_array(a0, a1, b, e0, e1, left), b, succ(leftright));
              close sorted(concat_array(a0, a1, b, e0, e1, left), b, e1);
            }
          }
        }
      }
    }

    lemma void concat_array3(int*a, array(int,int) end, array(int,int) a0, array(int,int) a1, int b0, int e0, int e1, int bound, nat left, nat right)
    	requires array_model(a,b0,e0,a0) &*& array_model(a,e0,e1,a1) &*& same_multiset(end, a0, b0, e0) &*& same_multiset(end, a1, e0, e1) &*&
    	         sorted(a0,b0,e0) &*& sorted(a1,e0+1,e1) &*& minore(a0,b0,nat_of_int(e0-b0),bound) &*&
    		 majore(a1,e0+1,right,bound) &*& bound == select(a1, e0) &*&
    		 b0 <= e0 &*& e0 < e1 &*& int_diff(b0, e0, left) == true &*& int_diff(e0+1, e1, right) == true;
    	ensures array_model(a,b0,e1,?res) &*& same_multiset(res,end,b0,e1) &*& sorted(res,b0,e1);
    	{
    	  array(int, int) res = concat_array(a0, a1, b0, e0, e1, left);
    	  concat_array_model(a, a0, a1, b0, e0, e1, left);
    	  open sorted(a1, e0+1, e1);
    	  dup_majore(a1, e0+1, right, bound);
    	  int_diff_le(e0+1, e1, right);
    	  sorted_majore(a1, e0, right);
    	  close sorted(a1, e0, e1);
    	  int_diff_le(b0, e0, left);
    	  concat_array_sorted(a0, a1, b0, e0, e1, left, right);
    	  concat_array_same_multiset_left(a0, a1, b0, e0, e1, left);
    	  same_multiset_trans(end, a0, res, b0, e0);
    	  concat_array_same_multiset_right(a0, a1, b0, e0, e1, left);
    	  same_multiset_trans(end, a1, res, e0, e1);
    	  same_multiset_concat(end, res, b0, e0, e1);
    	  same_multiset_sym(end, res, b0, e1);
    	}
                     
     lemma void multiset_trans(array(int,int) arr, array(int,int) arr0, array(int,int) arr1, int b, int e)
     	requires same_multiset(arr0,arr,b,e) &*& same_multiset(arr1,arr,b,e);
     	ensures same_multiset(arr0,arr1,b,e);
     	{ same_multiset_sym(arr1, arr, b, e);
     	  same_multiset_trans(arr0, arr, arr1, b, e); }
@*/
void quicksort (int* a, int lo, int hi)
//@ requires array_model(a, lo, hi+1, ?start);
//@ ensures array_model(a, lo, hi+1, ?end) &*& same_multiset(start, end,lo,hi+1) &*& sorted(end,lo,hi+1);
{
  if (lo > hi){
   //@ empty_sorted(start,lo,hi+1);
   //@ same_multiset_refl(start,lo,hi+1);
   return;
  }else{
   //@ array_model_select_unfold(a,lo,hi+1,start,hi);
   int p = partition(a, lo, hi);
   //@ assert array_model(a,lo,hi+1,?end);
   //@ array_model_select_unfold(a,lo,hi+1,end,p);
   quicksort(a, lo, p-1);
   //@ assert array_model(a,lo,p,?end0);
   quicksort(a, p+1, hi);
   //@ assert array_model(a,p+1,hi+1,?end1);
   //@ empty_array(a,p,end1);
   //@ array_model_store_fold(a,p,hi+1,end1,p);
   //@ open array_model(a, hi+1, hi+1, start);
   //@ same_multi_etend(end,end1, p+1, hi+1);
   //@ open sorted(end1, p+1, hi+1);
   //@ sorted_etend(end1, p+1, nat_of_int(hi-p), p, select(end,p));
   //@ close sorted(store(end1, p, select(end, p)), p+1, hi+1);
   //@ nat left = int_diff_always(lo, p);
   //@ int_diff_le(lo, p, left);
   //@ nat right = int_diff_always(p+1, hi+1);
   //@ int_diff_le(p+1, hi+1, right);
   //@ open minore(end, lo, left, select(end, p));
   //@ open same_multiset(end, end0, lo, p);
   //@ close minore(end0, lo, left, select(end, p));
   //@ close same_multiset(end, end0, lo, p);
   //@ open majore(end, p+1, right, select(end, p));
   //@ open same_multiset(end, store(end1, p, select(end, p)), p, hi+1);
   //@ note (array_multiset(p, succ(right), end) == array_multiset(p, succ(right), store(end1, p, select(end, p))));
   //@ regular_multiset_add(array_multiset(p+1, right, end), array_multiset(p+1, right, store(end1, p, select(end, p))), select(end, p));
   //@ close majore(store(end1, p, select(end, p)), p+1, right, select(end, p));
   //@ close same_multiset(end, store(end1, p, select(end, p)), p, hi+1);
   //@ concat_array3(a,end,end0,store(end1,p, select(end,p)),lo,p,hi+1, select(end,p), left, right);
   //@ assert array_model(a,lo,hi+1,?res);
   //@ multiset_trans(end,start,res, lo, hi+1);
  }
}
