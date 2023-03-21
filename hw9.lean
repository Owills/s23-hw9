
/- Problem 1: Append and Reverse -/

/- Prove the following theorems. If you can't complete a proof, 
you can use the tactic `sorry` for any part that you are 
unable to complete. -/

/- Note that we again define our own append reverse, 
this time using the built in types -/

-- part p1
def app : List Nat -> List Nat -> List Nat
  | List.nil,       bs => bs
  | List.cons a as, bs => List.cons a (app as bs)

def rev : List Nat -> List Nat 
  | List.nil => List.nil
  | List.cons a L => app (rev L) (List.cons a List.nil) 

-- 6 lines
theorem app_nil : forall (l : List Nat), app l [] = l := 
  by intros l
     induction l
     rfl
     case cons head tail ih => simp [app]
                               assumption

-- 6 lines
theorem app_assoc : forall (l1 l2 l3 : List Nat),
  app (app l1 l2) l3 = app l1 (app l2 l3) := 
 by intros l1
    induction l1
    case nil => simp [app]
    case cons head tail ih => simp [app]
                              assumption

-- 8 lines
theorem rev_app_distr: forall l1 l2 : List Nat,
  rev (app l1 l2) = app (rev l2) (rev l1) := 
 by intros l1
    induction l1
    case nil => simp [app]
                simp [rev]
                simp [app_nil]
    case cons head tail ih => intros l2
                              simp [rev, app]
                              rw [ih]
                              simp [app_assoc]
                              


-- 8 lines
theorem rev_involutive : forall l : List Nat,
  rev (rev l) = l := 
 by intros l
    induction l
    rfl
    case cons head tail ih => simp [rev]
                              simp [rev_app_distr]
                              rw [ih]
                              simp [rev]
                              simp [app]
-- part p1


/- Problem 2: Evenness (and Relations) -/

/- Prove the following theorems. If you can't complete a proof, 
you can use the tactic `sorry` for any part that you are 
unable to complete. -/

-- part p2
inductive ev : Nat -> Prop 
| O : ev 0
| SS (n : Nat) (H : ev n) : ev (Nat.succ (Nat.succ n))

def double : Nat -> Nat
| 0 => 0
| Nat.succ n => Nat.succ (Nat.succ (double n))

-- 5 lines
theorem ev_double : forall n, ev (double n) := 
 by intros n
    induction n
    case zero => simp [double]
                 apply ev.O
    case succ n ih => simp [double]
                      apply ev.SS
                      assumption

-- 15 lines
theorem ev_sum : forall n m, ev n -> ev m -> ev (Nat.add n m) := 
 by intros n m evn evm
    induction evn 
    case O => simp [*]
    case SS r IH1 IH2 => simp []
                         rw [Nat.add_comm] 
                         simp [Nat.add_succ]
                         constructor
                         simp [] at IH2
                         rw [Nat.add_comm] 
                         assumption



    

-- 3 lines
theorem three_not_ev : Not (ev 3) := 
 by intros n
    cases n
    contradiction
    


inductive ev' : Nat -> Prop :=
  | O : ev' 0
  | SSO : ev' 2
  | sum n m (Hn : ev' n) (Hm : ev' m) : ev' (Nat.add n m)

-- 21 lines
theorem ev'_ev : forall n, ev' n <-> ev n := 
 by intros n
    constructor 
    case mp => intros H
               induction H
               case O => constructor
               case SSO => constructor
                           constructor
               case sum  => apply ev_sum <;> assumption
    case mpr => intros H
                induction H
                case O => constructor
                case SS => simp [Nat.succ_eq_add_one]
                           have r : 1 + 1 = 2 := rfl
                           rw [Nat.add_assoc]
                           rw [r] 
                           constructor
                           case Hn => assumption
                           case Hm => constructor





-- part p2

/- Problem 3: Subsequences -/

/- Prove the following theorems. If you can't complete a proof, 
you can use the tactic `sorry` for any part that you are 
unable to complete. -/

-- part p3
inductive subseq : List Nat -> List Nat -> Prop
| empty : subseq [] []
| include x l1 l2 (H : subseq l1 l2) : subseq (x::l1) (x::l2)
| skip x l1 l2 (H : subseq l1 l2) : subseq l1 (x::l2)

-- 6 lines
theorem subseq_refl : forall (l : List Nat), 
  subseq l l :=
 by intros l
    induction l
    constructor
    case cons head tails ih => constructor
                               assumption

-- 5 lines
theorem subseq_empty : forall l, subseq [] l := 
 by intros l 
    induction l 
    constructor
    case cons head tail ih => constructor
                              assumption

-- 13 lines
theorem subseq_app : forall (l1 l2 l3 : List Nat),
  subseq l1 l2 ->
  subseq l1 (List.append l2 l3) :=
 by intros l1 l2 l3 h
    induction h 
    case empty => simp
                  induction l3
                  case nil => constructor
                  case cons head tail h => constructor
                                           assumption
    case include x q r _ l => constructor
                              assumption
    case skip x q r _ l => constructor
                           assumption
                                         



                              


-- part p3

/- Problem 4: Insertion Sort -/


/- Prove the following theorems. If you can't complete a proof, 
you can use the tactic `sorry` for any part that you are 
unable to complete. -/

-- part p4
def insert : Nat -> List Nat -> List Nat
| y, [] => [y]
| y, x::xs => if Nat.ble y x 
              then y :: x :: xs 
              else x :: insert y xs

def isort : List Nat -> List Nat
| []      => []
| x :: xs => insert x (isort xs) 

inductive All : {T : Type} -> (T -> Prop) -> List T -> Prop
| nil : All P []
| cons : forall x L, P x -> All P L -> All P (x :: L)

inductive Sorted : List Nat -> Prop
| nil : Sorted []
| cons : forall n l, Sorted l -> 
                     All (Nat.le n) l ->
                     Sorted (n :: l)


theorem all_trans : forall (P : T -> Prop) (Q : T -> Prop) L,
  All P L ->
  (forall x, P x -> Q x) ->
  All Q L := 
 by intros P Q L Hall PtoQ
    induction Hall
    case nil => constructor
    case cons P x L _ HL =>
      constructor
      apply PtoQ
      assumption
      assumption

-- 23 lines
theorem insert_le : forall n x l,
  All (Nat.le n) l ->
  Nat.le n x ->
  All (Nat.le n) (insert x l) := 
 by intros n m l h1 h2
    induction h1
    case nil => simp [insert]
                constructor
                case a => assumption
                case a => constructor
    case cons head tail q p r => simp only [insert]
                                 generalize t : Nat.ble m head = q
                                 cases q
                                 case false => simp only []
                                               rw [ite_false]
                                               constructor <;> assumption
                                  case true => simp only []
                                               rw [ite_true]
                                               constructor 
                                               case a => assumption
                                               case a => constructor
                                                          case a => assumption
                                                          case a => assumption

    

                            

                               

theorem ble_inv : forall a b, 
                  Nat.ble a b = false
               -> Nat.ble b a = true := 
 by intros a b H
    rw [Nat.ble_eq]
    cases (Nat.le_total b a)
    assumption
    rw [<- Nat.not_lt_eq]
    rw [<- Bool.not_eq_true] at H
    rw [Nat.ble_eq] at H
    contradiction

-- 37 lines
theorem insert_sorted : forall x l, 
  Sorted l ->
  Sorted (insert x l) := 
 by intros n l h
    induction h
    case nil => simp [insert]
                constructor
                case a => constructor
                case a => constructor
    case cons head tail h1 h2 h3 => simp only [insert]
                                    generalize r : Nat.ble n head = q
                                    cases q 
                                    case false => simp only []
                                                  rw [ite_false]
                                                  constructor
                                                  case a => assumption
                                                  case a => apply insert_le
                                                            case a => assumption
                                                            case a => have q : Nat.ble head n = true := by apply ble_inv
                                                                                                           case a => assumption
                                                                      simp [Nat.le_of_ble_eq_true] at q
                                                                      simp [*]
                                    case true => simp only []
                                                 rw [ite_true]
                                                 constructor
                                                 case a => constructor
                                                           case a => assumption
                                                           case a => assumption
                                                 case a => constructor
                                                           case a => simp [Nat.le_of_ble_eq_true] at r
                                                                     simp [*]
                                                           case a => apply all_trans 
                                                                     case a => apply h2
                                                                     case a => simp [*]
                                                                               simp [Nat.le_of_ble_eq_true] at r
                                                                               intros x as
                                                                               apply Nat.le_trans
                                                                               assumption
                                                                               assumption
                                                                       
                                                                      
                                                            
                                    

-- 8 lines
theorem isort_sorted : forall l, Sorted (isort l) :=
 by intros l 
    induction l
    case nil => simp [isort]
                constructor
    case cons head tail ih => apply insert_sorted
                              case a => assumption


inductive Permutation : {T : Type} -> List T -> List T -> Prop
| nil   : Permutation [] []
| skip  : forall (x : A) (l l' : List A),
          Permutation l l' ->
          Permutation (x :: l) (x :: l')
| swap  : forall (x y : A) (l : List A),
          Permutation (y :: x :: l) (x :: y :: l)
| trans : forall l l' l'' : List A,
          Permutation l l' ->
          Permutation l' l'' ->
          Permutation l l''

example : Permutation [true,true,false] [false,true,true] :=
 by apply Permutation.trans (l' := [true,false,true])
    . apply Permutation.skip
      apply Permutation.swap
    . apply Permutation.swap

-- 6 lines
theorem perm_refl : forall {T : Type} (l : List T), 
  Permutation l l := 
 by intros t l 
    induction l
    case nil => constructor
    case cons => constructor
                 assumption 

-- 10 lines
theorem perm_length : forall {T : Type} (l1 l2 : List T), 
  Permutation l1 l2 -> l1.length = l2.length :=
 by intros t l1 l2 h
    induction h
    case nil => rfl
    case skip => simp [*]
    case swap => simp [*]
    case trans => simp [*]
    

-- 12 lines
theorem perm_sym : forall {T : Type} (l1 l2 : List T), 
  Permutation l1 l2 -> Permutation l2 l1 :=
 by intros t l1 l2 h
    induction h 
    case nil => constructor
    case skip => constructor
                 assumption
    case swap => constructor
    case trans => constructor <;>
                  assumption


-- 18 lines
theorem insert_perm : forall x l, 
  Permutation (x :: l) (insert x l) :=
 by intros x l 
    revert x  
    induction l <;> intros x
    case nil => constructor
                constructor
    case cons head tail ih => simp only [insert]
                              generalize r : Nat.ble x head = q
                              cases q
                              case false => simp only []
                                            rw [ite_false]
                                            apply Permutation.trans
                                            case a => apply Permutation.skip
                                                      apply ih 
                                            case a => apply Permutation.trans
                                                      case a => constructor
                                                                apply perm_sym
                                                                apply ih 
                                                      case a =>  apply perm_sym
                                                                 case a => constructor
                                                                           case a => constructor
                                                                                     apply perm_sym
                                                                                     apply ih 
                                                                           case a => constructor    
                              case true => simp only []
                                           rw [ite_true]
                                           constructor
                                           case a => constructor
                                                     apply perm_refl


                                         
                                         
-- 10 lines
theorem isort_perm : forall l, Permutation l (isort l) :=
 by intros l 
    induction l
    case nil => constructor
    case cons head tail ih => simp [isort]
                              constructor
                              case a => constructor
                                        case a => assumption
                              case a => apply insert_perm   
                              
                                                             

                  

-- part p4
