theory Huffman_Nuns
imports "../Nunchaku"
begin

declare Int_Un_distrib [simp]
        Int_Un_distrib2 [simp]
        max.absorb1 [simp]
        max.absorb2 [simp]

datatype 'a tree =
  Leaf nat 'a
| InnerNode nat "('a tree)" "('a tree)"

type_synonym 'a forest = "'a tree list"

primrec alphabet :: "'a tree \<Rightarrow> 'a \<Rightarrow> bool" where
"alphabet (Leaf w a) b = (a = b)" |
"alphabet (InnerNode w t1 t2) a = (alphabet t1 a \<or> alphabet t2 a)"

primrec alphabetF :: "'a forest \<Rightarrow> 'a \<Rightarrow> bool" where
"alphabetF [] _ = False" |
"alphabetF (t # ts) a = (alphabet t a \<or> alphabetF ts a)"

lemma exists_in_alphabet:
"\<exists>a. alphabet t a"
by (induct t) auto

primrec consistent :: "'a tree \<Rightarrow> bool" where
"consistent (Leaf w a) = True" |
"consistent (InnerNode w t1 t2) =
     (consistent t1 \<and> consistent t2 \<and> (\<forall>a. \<not> alphabet t1 a \<or> \<not> alphabet t2 a))"

primrec consistentF :: "'a forest \<Rightarrow> bool" where
"consistentF [] = True" |
"consistentF (t # ts) =
     (consistent t \<and> consistentF ts \<and> (\<forall>a. \<not> alphabet t a \<or> \<not> alphabetF ts a))"

lemma tree_induct_consistent [consumes 1, case_names base step1 step2 step3]:
"\<lbrakk>consistent t;
  \<And>wb b a. P (Leaf wb b) a;
  \<And>w t1 t2 a.
     \<lbrakk>consistent t1; consistent t2; (\<forall>a. \<not> alphabet t1 a \<or> alphabet t2 a);
      alphabet t1 a; \<not> alphabet t2 a; P t1 a; P t2 a\<rbrakk> \<Longrightarrow>
     P (InnerNode w t1 t2) a;
  \<And>w t1 t2 a.
     \<lbrakk>consistent t1; consistent t2; (\<forall>a. \<not> alphabet t1 a \<or> alphabet t2 a);
      ~ alphabet t1 a; alphabet t2 a; P t1 a; P t2 a\<rbrakk> \<Longrightarrow>
     P (InnerNode w t1 t2) a;
  \<And>w t1 t2 a.
     \<lbrakk>consistent t1; consistent t2; (\<forall>a. \<not> alphabet t1 a \<or> alphabet t2 a);
      ~ alphabet t1 a; ~ alphabet t2 a; P t1 a; P t2 a\<rbrakk> \<Longrightarrow>
     P (InnerNode w t1 t2) a\<rbrakk> \<Longrightarrow>
 P t a"
sorry

primrec depth :: "'a tree \<Rightarrow> 'a \<Rightarrow> nat" where
"depth (Leaf w b) a = 0" |
"depth (InnerNode w t1 t2) a =
     (if alphabet t1 a then depth t1 a + 1
      else if alphabet t2 a then depth t2 a + 1
      else 0)"

primrec height :: "'a tree \<Rightarrow> nat" where
"height (Leaf w a) = 0" |
"height (InnerNode w t1 t2) = max (height t1) (height t2) + 1"

primrec heightF :: "'a forest \<Rightarrow> nat" where
"heightF [] = 0" |
"heightF (t # ts) = max (height t) (heightF ts)"

lemma depth_le_height:
"depth t a \<le> height t"
by (induct t) auto

lemma exists_at_height:
"consistent t \<Longrightarrow> \<exists>a. alphabet t a \<and> depth t a = height t"
sorry

lemma depth_max_heightE_left [elim!]:
"\<lbrakk>depth t1 a = max (height t1) (height t2);
  \<lbrakk>depth t1 a = height t1; height t1 \<ge> height t2\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow>
 P"
by (cut_tac t = t1 and a = a in depth_le_height) simp

lemma depth_max_heightE_right [elim!]:
"\<lbrakk>depth t2 a = max (height t1) (height t2);
  \<lbrakk>depth t2 a = height t2; height t2 \<ge> height t1\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow>
 P"
by (cut_tac t = t2 and a = a in depth_le_height) simp

lemma height_gt_0_alphabet_eq_imp_height_gt_0:
assumes "height t > 0" "consistent t" "\<forall>a. alphabet t a = alphabet u a"
shows "height u > 0"
sorry

primrec freq :: "'a tree \<Rightarrow> 'a \<Rightarrow> nat" where
"freq (Leaf w a) b = (if b = a then w else 0)" |
"freq (InnerNode w t1 t2) b = (freq t1 b + freq t2 b)"

primrec freqF :: "'a forest \<Rightarrow> 'a \<Rightarrow> nat" where
"freqF [] = (\<lambda>b. 0)" |
"freqF (t # ts) = (\<lambda>b. freq t b + freqF ts b)"

lemma notin_alphabet_imp_freq_0 [simp]:
"~ alphabet t a \<Longrightarrow> freq t a = 0"
by (induct t) simp+

lemma notin_alphabetF_imp_freqF_0 [simp]:
"~ alphabetF ts a \<Longrightarrow> freqF ts a = 0"
by (induct ts) simp+

lemma freq_0_right [simp]:
"\<lbrakk>\<forall>a. ~ alphabet t1 a \<or> \<not> alphabet t2 a; alphabet t1 a\<rbrakk> \<Longrightarrow> freq t2 a = 0"
by (auto intro: notin_alphabet_imp_freq_0 simp: disjoint_iff_not_equal)

lemma freq_0_left [simp]:
"\<lbrakk>\<forall>a. ~ alphabet t1 a \<or> \<not> alphabet t2 a; alphabet t2 a\<rbrakk> \<Longrightarrow> freq t1 a = 0"
sorry

lemma heightF_0_imp_Leaf_freqF_in_set:
"\<lbrakk>consistentF ts; heightF ts = 0; alphabetF ts a\<rbrakk> \<Longrightarrow>
 Leaf (freqF ts a) a \<in> set ts"
sorry

primrec weight :: "'a tree \<Rightarrow> nat" where
"weight (Leaf w a) = w" |
"weight (InnerNode w t1 t2) = weight t1 + weight t2"

(*<*)
lemma weight_eq_Sum_freq:
"consistent t \<Longrightarrow> weight t = (\<Sum>a \<in> UNIV. freq t a)"
sorry

primrec cost :: "'a tree \<Rightarrow> nat" where
"cost (Leaf w a) = 0" |
"cost (InnerNode w t1 t2) = weight t1 + cost t1 + weight t2 + cost t2"

(*<*)
theorem cost_eq_Sum_freq_mult_depth:
"consistent t \<Longrightarrow> cost t = (\<Sum>a \<in> UNIV. freq t a * depth t a)"
(*>*)
sorry

lemma height_0_imp_cost_0 [simp]:
"height t = 0 \<Longrightarrow> cost t = 0"
by (case_tac t) simp+

definition optimum :: "'a tree \<Rightarrow> bool" where
"optimum t \<equiv>
     \<forall>u. consistent u \<longrightarrow> (ALL x. alphabet t x = alphabet u x) \<longrightarrow> (ALL x. freq t x = freq u x) \<longrightarrow>
         cost t \<le> cost u"

primrec cachedWeight :: "'a tree \<Rightarrow> nat" where
"cachedWeight (Leaf w a) = w" |
"cachedWeight (InnerNode w t1 t2) = w"

lemma height_0_imp_cachedWeight_eq_weight [simp]:
"height t = 0 \<Longrightarrow> cachedWeight t = weight t"
by (case_tac t) simp+

definition uniteTrees :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"uniteTrees t1 t2 \<equiv> InnerNode (cachedWeight t1 + cachedWeight t2) t1 t2"

lemma freq_uniteTrees [simp]:
"freq (uniteTrees t1 t2) = (\<lambda>a. freq t1 a + freq t2 a)"
by (simp add: uniteTrees_def)

primrec insortTree :: "'a tree \<Rightarrow> 'a forest \<Rightarrow> 'a forest" where
"insortTree u [] = [u]" |
"insortTree u (t # ts) =
     (if cachedWeight u \<le> cachedWeight t then u # t # ts
                                         else t # insortTree u ts)"

lemma length_insortTree [simp]:
"length (insortTree t ts) = length ts + 1"
by (induct ts) simp+

lemma insortTree_ne_Nil [simp]:
"insortTree t ts \<noteq> []"
by (case_tac ts) simp+

lemma freqF_insortTree [simp]:
"freqF (insortTree t ts) = (\<lambda>a. freq t a + freqF ts a)"
by (induct ts) (simp add: ext)+

lemma heightF_insortTree [simp]:
"heightF (insortTree t ts) = max (height t) (heightF ts)"
by (induct ts) auto

fun huffman :: "'a forest \<Rightarrow> 'a tree" where
"huffman [t] = t" |
"huffman (t1 # t2 # ts) = huffman (insortTree (uniteTrees t1 t2) ts)"

theorem freq_huffman [simp]:
"ts \<noteq> [] \<Longrightarrow> freq (huffman ts) = freqF ts"
by (induct ts rule: huffman.induct) (auto simp: ext)

fun sibling :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a" where
"sibling (Leaf wb b) a = a" |
"sibling (InnerNode w (Leaf wb b) (Leaf wc c)) a =
     (if a = b then c else if a = c then b else a)" |
"sibling (InnerNode w (InnerNode X L R) t2) a =
     (if alphabet (InnerNode X L R) a then sibling (InnerNode X L R) a
      else if alphabet t2 a then sibling t2 a
      else a)" |
"sibling (InnerNode w (Leaf wb b) (InnerNode X L R)) a =
     (if alphabet (Leaf wb b) a then sibling (Leaf wb b) a
      else if alphabet (InnerNode X L R) a then sibling (InnerNode X L R) a
      else a)"

lemma notin_alphabet_imp_sibling_id [simp]:
"~ alphabet t a \<Longrightarrow> sibling t a = a"
sorry

lemma height_0_imp_sibling_id [simp]:
"height t = 0 \<Longrightarrow> sibling t a = a"
by (case_tac t) simp+

lemma height_gt_0_in_alphabet_imp_sibling_left [simp]:
"\<lbrakk>height t1 > 0; alphabet t1 a\<rbrakk> \<Longrightarrow>
 sibling (InnerNode w t1 t2) a = sibling t1 a"
by (case_tac t1) simp+

lemma height_gt_0_in_alphabet_imp_sibling_right [simp]:
"\<lbrakk>height t2 > 0; alphabet t1 a\<rbrakk> \<Longrightarrow>
 sibling (InnerNode w t1 t2) a = sibling t1 a"
sorry

lemma height_gt_0_notin_alphabet_imp_sibling_left [simp]:
"\<lbrakk>height t1 > 0; ~ alphabet t1 a\<rbrakk> \<Longrightarrow>
 sibling (InnerNode w t1 t2) a = sibling t2 a"
by (case_tac t1) simp+

lemma height_gt_0_notin_alphabet_imp_sibling_right [simp]:
"\<lbrakk>height t2 > 0; ~ alphabet t1 a\<rbrakk> \<Longrightarrow>
 sibling (InnerNode w t1 t2) a = sibling t2 a"
sorry

lemma either_height_gt_0_imp_sibling [simp]:
"height t1 > 0 \<or> height t2 > 0 \<Longrightarrow>
 sibling (InnerNode w t1 t2) a =
     (if alphabet t1 a then sibling t1 a else sibling t2 a)"
by auto

lemma in_alphabet_imp_sibling_in_alphabet:
"alphabet t a \<Longrightarrow> alphabet t (sibling t a)"
by (induct t a rule: sibling.induct) auto

lemma sibling_ne_imp_sibling_in_alphabet:
"sibling t a \<noteq> a \<Longrightarrow> alphabet t (sibling t a)"
by (metis notin_alphabet_imp_sibling_id in_alphabet_imp_sibling_in_alphabet)

lemma sibling_sibling_id [simp]:
"consistent t \<Longrightarrow> sibling t (sibling t a) = a"
sorry

lemma sibling_reciprocal:
"\<lbrakk>consistent t; sibling t a = b\<rbrakk> \<Longrightarrow> sibling t b = a"
by auto

lemma depth_height_imp_sibling_ne:
"\<lbrakk>consistent t; depth t a = height t; height t > 0; alphabet t a\<rbrakk> \<Longrightarrow>
 sibling t a \<noteq> a"
by (induct t a rule: sibling_induct_consistent) auto

lemma depth_sibling [simp]:
"consistent t \<Longrightarrow> depth t (sibling t a) = depth t a"
by (induct t a rule: sibling_induct_consistent) simp+

primrec swapLeaves :: "'a tree \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"swapLeaves (Leaf wc c) wa a wb b =
     (if c = a then Leaf wb b else if c = b then Leaf wa a else Leaf wc c)" |
"swapLeaves (InnerNode w t1 t2) wa a wb b =
     InnerNode w (swapLeaves t1 wa a wb b) (swapLeaves t2 wa a wb b)"

(* GOOD EXAMPLES *)

lemma "swapLeaves t wa a wa a = t"
(*
nunchaku[overlord, debug]
*)
oops

lemma "swapLeaves t (freq t a) a (freq t a) a = t"
(*
nunchaku[overlord, debug]
*)
oops

lemma "consistent t \<Longrightarrow> swapLeaves t (freq t a) a (freq t a) a = t"
(*
nunchaku[overlord, debug]
*)
oops

lemma swapLeaves_id_when_notin_alphabet [simp]:
"~ alphabet t a \<Longrightarrow> ~ alphabet t b \<Longrightarrow> swapLeaves t w a w' b = t"
(* nunchaku[debug, overlord] *)
sorry

lemma swapLeaves_id [simp]:
"consistent t \<Longrightarrow> swapLeaves t (freq t a) a (freq t a) a = t"
by (induct t a rule: tree_induct_consistent) simp+

primrec setFreq :: "'a tree \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"setFreq (Leaf wc c) wa a =
     (if c = a then Leaf wa a else Leaf wc c)" |
"setFreq (InnerNode w t1 t2) wa a =
     InnerNode w (setFreq t1 wa a) (setFreq t2 wa a)"

lemma alphabet_swapLeaves:
"alphabet t a \<Longrightarrow> alphabet (setFreq t wa a) a"
apply (induct t)
apply auto[1]
by (induct t) auto

lemma consistent_swapLeaves [simp]:
"consistent t \<Longrightarrow> consistent (swapLeaves t wa a wb b)"
by (induct t) (auto simp: alphabet_swapLeaves)

lemma depth_swapLeaves_neither [simp]:
"\<lbrakk>consistent t; c \<noteq> a; c \<noteq> b\<rbrakk> \<Longrightarrow> depth (swapLeaves t wa a wb b) c = depth t c"
(*nunchaku[debug, overlord]*)
by (induct t a rule: tree_induct_consistent) (auto simp: alphabet_swapLeaves)

lemma height_swapLeaves [simp]:
"height (swapLeaves t wa a wb b) = height t"
by (induct t) simp+

lemma freq_swapLeaves [simp]:
"\<lbrakk>consistent t; a \<noteq> b\<rbrakk> \<Longrightarrow>
 freq (swapLeaves t wa a wb b) =
     (\<lambda>c. if c = a then if alphabet t b then wa else 0
          else if c = b then if alphabet t a then wb else 0
          else freq t c)"
apply (rule ext)
apply (induct t)
by auto

lemma weight_swapLeaves:
"\<lbrakk>consistent t; a \<noteq> b\<rbrakk> \<Longrightarrow>
 if alphabet t a then
   if alphabet t b then
     weight (swapLeaves t wa a wb b) + freq t a + freq t b =
         weight t + wa + wb
   else
     weight (swapLeaves t wa a wb b) + freq t a = weight t + wb
 else
   if alphabet t b then
     weight (swapLeaves t wa a wb b) + freq t b = weight t + wa
   else
     weight (swapLeaves t wa a wb b) = weight t"
proof (induct t a rule: tree_induct_consistent)
  case base thus ?case by clarsimp
next
  case (step1 w t1 t2 a) show ?case
  proof cases
    assume "alphabet t1 b"
    moreover hence "~ alphabet t2 b" using step1 by auto
    ultimately show ?case using step1 by simp
  next
    assume "~ alphabet t1 b" thus ?case using step1 by auto
  qed
next
  case (step2 w t1 t2 a) show ?case
  proof cases
    assume "alphabet t1 b"
    moreover hence "~ alphabet t2 b" using step2 by auto
    ultimately show ?case using step2 by simp
  next
    assume "~ alphabet t1 b" thus ?case using step2 by auto
  qed
next
  case (step3 w t1 t2 a) show ?case
  proof cases
    assume "alphabet t1 b"
    moreover hence "~ alphabet t2 b" using step3 by auto
    ultimately show ?case using step3 by simp
  next
    assume "~ alphabet t1 b" thus ?case using step3 by auto
  qed
qed

lemma cost_swapLeaves:
"\<lbrakk>consistent t; a \<noteq> b\<rbrakk> \<Longrightarrow>
 if alphabet t a then
   if alphabet t b then
     cost (swapLeaves t wa a wb b) + freq t a * depth t a
     + freq t b * depth t b =
         cost t + wa * depth t b + wb * depth t a
   else
     cost (swapLeaves t wa a wb b) + freq t a * depth t a =
         cost t + wb * depth t a
 else
   if alphabet t b then
     cost (swapLeaves t wa a wb b) + freq t b * depth t b =
         cost t + wa * depth t b
   else
     cost (swapLeaves t wa a wb b) = cost t"
proof (induct t)
  case Leaf show ?case by simp
next
  case (InnerNode w t1 t2)
  note c = `consistent (InnerNode w t1 t2)`
  note hyps = InnerNode
  have w1: "if alphabet t1 a then
              if alphabet t1 b then
                weight (swapLeaves t1 wa a wb b) + freq t1 a + freq t1 b =
                    weight t1 + wa + wb
                  else
                weight (swapLeaves t1 wa a wb b) + freq t1 a = weight t1 + wb
            else
              if alphabet t1 b then
                weight (swapLeaves t1 wa a wb b) + freq t1 b = weight t1 + wa
              else
                weight (swapLeaves t1 wa a wb b) = weight t1" using hyps
    by (simp add: weight_swapLeaves)
  have w2: "if alphabet t2 a then
              if alphabet t2 b then
                weight (swapLeaves t2 wa a wb b) + freq t2 a + freq t2 b =
                    weight t2 + wa + wb
              else
                weight (swapLeaves t2 wa a wb b) + freq t2 a = weight t2 + wb
            else
              if alphabet t2 b then
                weight (swapLeaves t2 wa a wb b) + freq t2 b = weight t2 + wa
              else
                weight (swapLeaves t2 wa a wb b) = weight t2" using hyps
    by (simp add: weight_swapLeaves)
  show ?case
  proof cases
    assume a1: "alphabet t1 a"
    hence a2: "~ alphabet t2 a" using c by auto
    show ?case
    proof cases
      assume b1: "alphabet t1 b"
      hence "~ alphabet t2 b" using c by auto
      thus ?case using a1 a2 b1 w1 w2 hyps by simp
    next
      assume b1: "~ alphabet t1 b" show ?case
      proof cases
        assume "alphabet t2 b" thus ?case using a1 a2 b1 w1 w2 hyps by simp
      next
        assume "~ alphabet t2 b" thus ?case using a1 a2 b1 w1 w2 hyps by simp
      qed
    qed
  next
    assume a1: "~ alphabet t1 a" show ?case
    proof cases
      assume a2: "alphabet t2 a" show ?case
      proof cases
        assume b1: "alphabet t1 b"
        hence "~ alphabet t2 b" using c by auto
        thus ?case using a1 a2 b1 w1 w2 hyps by simp
      next
        assume b1: "~ alphabet t1 b" show ?case
        proof cases
          assume "alphabet t2 b" thus ?case using a1 a2 b1 w1 w2 hyps by simp
        next
          assume "~ alphabet t2 b" thus ?case using a1 a2 b1 w1 w2 hyps by simp
        qed
      qed
    next
      assume a2: "~ alphabet t2 a" show ?case
      proof cases
        assume b1: "alphabet t1 b"
        hence "~ alphabet t2 b" using c by auto
        thus ?case using a1 a2 b1 w1 w2 hyps by simp
      next
        assume b1: "~ alphabet t1 b" show ?case
        proof cases
          assume "alphabet t2 b" thus ?case using a1 a2 b1 w1 w2 hyps by simp
        next
          assume "~ alphabet t2 b" thus ?case using a1 a2 b1 w1 w2 hyps by simp
        qed
      qed
    qed
  qed
qed

lemma sibling_swapLeaves_sibling [simp]:
"\<lbrakk>consistent t; sibling t b \<noteq> b; a \<noteq> b\<rbrakk> \<Longrightarrow>
 sibling (swapLeaves t wa a ws (sibling t b)) a = b"
proof (induct t)
  case Leaf thus ?case by simp
next
  case (InnerNode w t1 t2)
  note hyps = InnerNode
  show ?case
  proof (cases "height t1 = 0")
    case True
    note h1 = True
    show ?thesis
    proof (cases t1)
      case (Leaf wc c)
      note l1 = Leaf
      show ?thesis
      proof (cases "height t2 = 0")
        case True
        note h2 = True
        show ?thesis
        proof (cases t2)
          case Leaf thus ?thesis using l1 hyps by auto metis+
        next
          case InnerNode thus ?thesis using h2 by simp
        qed
      next
        case False
        note h2 = False
        show ?thesis
        proof cases
          assume "c = b" thus ?thesis using l1 h2 hyps by simp
        next
          assume "c \<noteq> b"
          have "sibling t2 alphabet t2 b" using `c \<noteq> b` l1 h2 hyps
            by (simp add: sibling_ne_imp_sibling_in_alphabet)
          thus ?thesis using `c \<noteq> b` l1 h2 hyps by auto
        qed
      qed
    next
      case InnerNode thus ?thesis using h1 by simp
    qed
  next
    case False
    note h1 = False
    show ?thesis
    proof (cases "height t2 = 0")
      case True
      note h2 = True
      show ?thesis
      proof (cases t2)
        case (Leaf wd d)
        note l2 = Leaf
        show ?thesis
        proof cases
          assume "d = b" thus ?thesis using h1 l2 hyps by simp
        next
          assume "d \<noteq> b" show ?thesis
          proof (cases "alphabet t1 b")
            case True
            hence "sibling t1 alphabet t1 b" using `d \<noteq> b` h1 l2 hyps
              by (simp add: sibling_ne_imp_sibling_in_alphabet)
            thus ?thesis using True `d \<noteq> b` h1 l2 hyps
              by (simp add: alphabet_swapLeaves)
          next
            case False thus ?thesis using `d \<noteq> b` l2 hyps by simp
          qed
        qed
      next
        case InnerNode thus ?thesis using h2 by simp
      qed
    next
      case False
      note h2 = False
      show ?thesis
      proof (cases "alphabet t1 b")
        case True thus ?thesis using h1 h2 hyps by auto
      next
        case False
        note b1 = False
        show ?thesis
        proof (cases "alphabet t2 b")
          case True thus ?thesis using b1 h1 h2 hyps
            by (auto simp: in_alphabet_imp_sibling_in_alphabet
                           alphabet_swapLeaves)
        next
          case False thus ?thesis using b1 h1 h2 hyps by simp
        qed
      qed
    qed
  qed
qed

definition swapSyms :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"swapSyms t a b \<equiv> swapLeaves t (freq t a) a (freq t b) b"

lemma swapSyms_id [simp]:
"consistent t \<Longrightarrow> swapSyms t a a = t"
by (simp add: swapSyms_def)

lemma alphabet_swapSyms [simp]:
"\<lbrakk>alphabet t a; alphabet t b\<rbrakk> \<Longrightarrow> alphabet (swapSyms t a b) x = alphabet t x"
by (simp add: swapSyms_def alphabet_swapLeaves)

lemma consistent_swapSyms [simp]:
"consistent t \<Longrightarrow> consistent (swapSyms t a b)"
by (simp add: swapSyms_def)

lemma depth_swapSyms_neither [simp]:
"\<lbrakk>consistent t; c \<noteq> a; c \<noteq> b\<rbrakk> \<Longrightarrow>
 depth (swapSyms t a b) c = depth t c"
by (simp add: swapSyms_def)

lemma freq_swapSyms [simp]:
"\<lbrakk>consistent t; alphabet t a; alphabet t b\<rbrakk> \<Longrightarrow>
 freq (swapSyms t a b) = freq t"
by (case_tac "a = b") (simp add: swapSyms_def ext)+

lemma cost_swapSyms:
assumes "consistent t" "alphabet t a" "alphabet t b"
shows "cost (swapSyms t a b) + freq t a * depth t a + freq t b * depth t b =
           cost t + freq t a * depth t b + freq t b * depth t a"
proof cases
  assume "a = b" thus ?thesis using assms by simp
next
  assume "a \<noteq> b"
  moreover hence "cost (swapLeaves t (freq t a) a (freq t b) b)
                      + freq t a * depth t a + freq t b * depth t b =
                  cost t + freq t a * depth t b + freq t b * depth t a"
    using assms by (simp add: cost_swapLeaves)
  ultimately show ?thesis using assms by (simp add: swapSyms_def)
qed

lemma le_le_imp_sum_mult_le_sum_mult:
"\<lbrakk>i \<le> j; m \<le> (n::nat)\<rbrakk> \<Longrightarrow> i * n + j * m \<le> i * m + j * n"
apply (subgoal_tac "i * m + i * (n - m) + j * m \<le> i * m + j * m + j * (n - m)")
 apply (simp add: diff_mult_distrib2)
by simp

lemma cost_swapSyms_le:
assumes "consistent t" "alphabet t a" "alphabet t b" "freq t a \<le> freq t b"
        "depth t a \<le> depth t b"
shows "cost (swapSyms t a b) \<le> cost t"
proof -
  let ?aabb = "freq t a * depth t a + freq t b * depth t b"
  let ?abba = "freq t a * depth t b + freq t b * depth t a"
  have "?abba \<le> ?aabb" using assms(4-5)
    by (rule le_le_imp_sum_mult_le_sum_mult)
  have "cost (swapSyms t a b) + ?aabb = cost t + ?abba" using assms(1-3)
    by (simp add: cost_swapSyms add.assoc [THEN sym])
  also have "\<dots> \<le> cost t + ?aabb" using `?abba \<le> ?aabb` by simp
  finally show ?thesis using assms(4-5) by simp
qed

lemma sibling_swapSyms_sibling [simp]:
"\<lbrakk>consistent t; sibling t b \<noteq> b; a \<noteq> b\<rbrakk> \<Longrightarrow>
 sibling (swapSyms t a (sibling t b)) a = b"
by (simp add: swapSyms_def)

lemma sibling_swapSyms_other_sibling [simp]:
"\<lbrakk>consistent t; sibling t b \<noteq> a; sibling t b \<noteq> b; a \<noteq> b\<rbrakk> \<Longrightarrow>
 sibling (swapSyms t a b) (sibling t b) = a"
by (metis consistent_swapSyms sibling_swapSyms_sibling sibling_reciprocal)

definition swapFourSyms :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"swapFourSyms t a b c d \<equiv>
     if a = d then swapSyms t b c
     else if b = c then swapSyms t a d
     else swapSyms (swapSyms t a c) b d"

lemma alphabet_swapFourSyms [simp]:
"\<lbrakk>alphabet t a; alphabet t b; alphabet t c; alphabet t d'\<rbrakk> \<Longrightarrow>
 alphabet (swapFourSyms t a b c d) x = alphabet t x"
by (simp add: swapFourSyms_def)

lemma consistent_swapFourSyms [simp]:
"consistent t \<Longrightarrow> consistent (swapFourSyms t a b c d)"
by (simp add: swapFourSyms_def)

lemma freq_swapFourSyms [simp]:
"\<lbrakk>consistent t; alphabet t a; alphabet t b; alphabet t c;
  alphabet t d\<rbrakk> \<Longrightarrow>
 freq (swapFourSyms t a b c d) = freq t"
by (auto simp: swapFourSyms_def)

lemma sibling_swapFourSyms_when_4th_is_sibling:
assumes "consistent t" "alphabet t a" "alphabet t b" "alphabet t c"
        "a \<noteq> b" "sibling t c \<noteq> c"
shows "sibling (swapFourSyms t a b c (sibling t c)) a = b"
proof (cases "a \<noteq> sibling t c \<and> b \<noteq> c")
  case True show ?thesis
  proof -
    let ?d = "sibling t c"
    let ?ts = "swapFourSyms t a b c ?d"
    have abba: "(sibling ?ts a = b) = (sibling ?ts b = a)" using `consistent t`
      by (metis consistent_swapFourSyms sibling_reciprocal)
    have s: "sibling t c = sibling (swapSyms t a c) a" using True assms
      by (metis sibling_reciprocal sibling_swapSyms_sibling)
    have "sibling ?ts b = sibling (swapSyms t a c) ?d" using s True assms
      by (auto simp: swapFourSyms_def)
    also have "\<dots> = a" using True assms
      by (metis sibling_reciprocal sibling_swapSyms_other_sibling
          swapLeaves_id swapSyms_def)
    finally have "sibling ?ts b = a" .
    with abba show ?thesis ..
  qed
next
  case False thus ?thesis using assms
    by (auto intro: sibling_reciprocal simp: swapFourSyms_def)
qed

fun mergeSibling :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"mergeSibling (Leaf wb b) a = Leaf wb b" |
"mergeSibling (InnerNode w (Leaf wb b) (Leaf wc c)) a =
     (if a = b \<or> a = c then Leaf (wb + wc) a
      else InnerNode w (Leaf wb b) (Leaf wc c))" |
"mergeSibling (InnerNode w t1 t2) a =
     InnerNode w (mergeSibling t1 a) (mergeSibling t2 a)"

lemmas mergeSibling_induct_consistent = sibling_induct_consistent

lemma notin_alphabet_imp_mergeSibling_id [simp]:
"~ alphabet t a \<Longrightarrow> mergeSibling t a = t"
by (induct t a rule: mergeSibling.induct) simp+

lemma height_gt_0_imp_mergeSibling_left [simp]:
"height t1 > 0 \<Longrightarrow>
 mergeSibling (InnerNode w t1 t2) a =
     InnerNode w (mergeSibling t1 a) (mergeSibling t2 a)"
by (case_tac t1) simp+

lemma height_gt_0_imp_mergeSibling_right [simp]:
"height t2 > 0 \<Longrightarrow>
 mergeSibling (InnerNode w t1 t2) a =
     InnerNode w (mergeSibling t1 a) (mergeSibling t2 a)"
by (case_tac t2) simp+

lemma either_height_gt_0_imp_mergeSibling [simp]:
"height t1 > 0 \<or> height t2 > 0 \<Longrightarrow>
 mergeSibling (InnerNode w t1 t2) a =
     InnerNode w (mergeSibling t1 a) (mergeSibling t2 a)"
by auto

lemma alphabet_mergeSibling [simp]:
"\<lbrakk>consistent t; alphabet t a\<rbrakk> \<Longrightarrow>
 alphabet (mergeSibling t a) = (alphabet t - {sibling t a}) \<union> {a}"
by (induct t a rule: mergeSibling_induct_consistent) auto

lemma consistent_mergeSibling [simp]:
"consistent t \<Longrightarrow> consistent (mergeSibling t a)"
by (induct t a rule: mergeSibling_induct_consistent) auto

lemma freq_mergeSibling:
"\<lbrakk>consistent t; alphabet t a; sibling t a \<noteq> a\<rbrakk> \<Longrightarrow>
 freq (mergeSibling t a) =
     (\<lambda>c. if c = a then freq t a + freq t (sibling t a)
          else if c = sibling t a then 0
          else freq t c)"
by (induct t a rule: mergeSibling_induct_consistent)
   (auto simp: fun_eq_iff)

lemma weight_mergeSibling [simp]:
"weight (mergeSibling t a) = weight t"
by (induct t a rule: mergeSibling.induct) simp+

lemma cost_mergeSibling:
"\<lbrakk>consistent t; sibling t a \<noteq> a\<rbrakk> \<Longrightarrow>
 cost (mergeSibling t a) + freq t a + freq t (sibling t a) = cost t"
by (induct t a rule: mergeSibling_induct_consistent) auto

primrec splitLeaf :: "'a tree \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"splitLeaf (Leaf wc c) wa a wb b =
     (if c = a then InnerNode wc (Leaf wa a) (Leaf wb b) else Leaf wc c)" |
"splitLeaf (InnerNode w t1 t2) wa a wb b =
     InnerNode w (splitLeaf t1 wa a wb b) (splitLeaf t2 wa a wb b)"

primrec splitLeafF :: "'a forest \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a forest" where
"splitLeafF [] wa a wb b = []" |
"splitLeafF (t # ts) wa a wb b =
     splitLeaf t wa a wb b # splitLeafF ts wa a wb b"

lemma notin_alphabet_imp_splitLeaf_id [simp]:
"~ alphabet t a \<Longrightarrow> splitLeaf t wa a wb b = t"
by (induct t) simp+

lemma notin_alphabetF_imp_splitLeafF_id [simp]:
"a \<notin> alphabetF ts \<Longrightarrow> splitLeafF ts wa a wb b = ts"
by (induct ts) simp+

lemma alphabet_splitLeaf [simp]:
"alphabet (splitLeaf t wa a wb b) =
     (if alphabet t a then alphabet t \<union> {b} else alphabet t)"
by (induct t) simp+

lemma consistent_splitLeaf [simp]:
"\<lbrakk>consistent t; ~ alphabet t b\<rbrakk> \<Longrightarrow> consistent (splitLeaf t wa a wb b)"
by (induct t) auto

lemma freq_splitLeaf [simp]:
"\<lbrakk>consistent t; ~ alphabet t b\<rbrakk> \<Longrightarrow>
 freq (splitLeaf t wa a wb b) =
     (if alphabet t a then
        (\<lambda>c. if c = a then wa else if c = b then wb else freq t c)
      else
        freq t)"
by (induct t b rule: tree_induct_consistent) (rule ext, auto)+

lemma weight_splitLeaf [simp]:
"\<lbrakk>consistent t; alphabet t a; freq t a = wa + wb\<rbrakk> \<Longrightarrow>
 weight (splitLeaf t wa a wb b) = weight t"
by (induct t a rule: tree_induct_consistent) simp+

lemma cost_splitLeaf [simp]:
"\<lbrakk>consistent t; alphabet t a; freq t a = wa + wb\<rbrakk> \<Longrightarrow>
 cost (splitLeaf t wa a wb b) = cost t + wa + wb"
by (induct t a rule: tree_induct_consistent) simp+

fun sortedByWeight :: "'a forest \<Rightarrow> bool" where
"sortedByWeight [] = True" |
"sortedByWeight [t] = True" |
"sortedByWeight (t1 # t2 # ts) =
     (weight t1 \<le> weight t2 \<and> sortedByWeight (t2 # ts))"

lemma sortedByWeight_Cons_imp_sortedByWeight:
"sortedByWeight (t # ts) \<Longrightarrow> sortedByWeight ts"
by (case_tac ts) simp+

lemma sortedByWeight_Cons_imp_forall_weight_ge:
"sortedByWeight (t # ts) \<Longrightarrow> \<forall>u \<in> set ts. weight u \<ge> weight t"
proof (induct ts arbitrary: t)
  case Nil thus ?case by simp
next
  case (Cons u us) thus ?case by simp (metis le_trans)
qed

lemma sortedByWeight_insortTree:
"\<lbrakk>sortedByWeight ts; height t = 0; heightF ts = 0\<rbrakk> \<Longrightarrow>
 sortedByWeight (insortTree t ts)"
by (induct ts rule: sortedByWeight.induct) auto

definition minima :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"minima t a b \<equiv>
     alphabet t a \<and> alphabet t b \<and> a \<noteq> b \<and> freq t a \<le> freq t b
     \<and> (\<forall>alphabet t c. c \<noteq> a \<longrightarrow> c \<noteq> b \<longrightarrow>
                         freq t c \<ge> freq t a \<and> freq t c \<ge> freq t b)"

lemma cost_swapFourSyms_le:
assumes "consistent t" "minima t a b" "alphabet t c" "alphabet t d"
        "depth t c = height t" "depth t d = height t" "c \<noteq> d"
shows "cost (swapFourSyms t a b c d) \<le> cost t"
proof -
  note lems = swapFourSyms_def minima_def cost_swapSyms_le depth_le_height
  show ?thesis
  proof (cases "a \<noteq> d \<and> b \<noteq> c")
    case True show ?thesis
    proof cases
      assume "a = c" show ?thesis
      proof cases
        assume "b = d" thus ?thesis using `a = c` True assms
          by (simp add: lems)
      next
        assume "b \<noteq> d" thus ?thesis using `a = c` True assms
          by (simp add: lems)
      qed
    next
      assume "a \<noteq> c" show ?thesis
      proof cases
        assume "b = d" thus ?thesis using `a \<noteq> c` True assms
          by (simp add: lems)
      next
        assume "b \<noteq> d"
        have "cost (swapFourSyms t a b c d) \<le> cost (swapSyms t a c)"
          using `b \<noteq> d` `a \<noteq> c` True assms by (clarsimp simp: lems)
        also have "\<dots> \<le> cost t" using `b \<noteq> d` `a \<noteq> c` True assms
          by (clarsimp simp: lems)
        finally show ?thesis .
      qed
    qed
  next
    case False thus ?thesis using assms by (clarsimp simp: lems)
  qed
qed

lemma twice_freq_le_imp_minima:
"\<lbrakk>\<forall>alphabet t c. wa \<le> freq t c \<and> wb \<le> freq t c;
  alphabet u = alphabet t \<union> {b}; alphabet u a; a \<noteq> b;
  freq u = (\<lambda>c. if c = a then wa else if c = b then wb else freq t c);
  wa \<le> wb\<rbrakk> \<Longrightarrow>
 minima u a b"
by (simp add: minima_def)

lemma optimum_splitLeaf:
assumes "consistent t" "optimum t" "alphabet t a" "~ alphabet t b"
        "freq t a = wa + wb" "\<forall>alphabet t c. freq t c \<ge> wa \<and> freq t c \<ge> wb"
        "wa \<le> wb"
shows "optimum (splitLeaf t wa a wb b)"
proof (unfold optimum_def, clarify)
  fix u
  let ?t' = "splitLeaf t wa a wb b"
  assume cu: "consistent u"
         and au: "alphabet ?t' = alphabet u"
         and fu: "freq ?t' = freq u"
  show "cost ?t' \<le> cost u"
  proof (cases "height ?t' = 0")
    case True thus ?thesis by simp
  next
    case False
    hence hu: "height u > 0" using au assms
      by (auto intro: height_gt_0_alphabet_eq_imp_height_gt_0)
    have aa: "alphabet u a" using au assms by fastforce
    have ab: "alphabet u b" using au assms by fastforce
    have ab: "a \<noteq> b" using assms by blast
    from exists_at_height [OF cu]
    obtain c where ac: "alphabet u c" and dc: "depth u c = height u" ..
    let ?d = "sibling u c"
    have dc: "?d \<noteq> c" using dc cu hu ac by (metis depth_height_imp_sibling_ne)
    have ad: "?alphabet u d" using dc
      by (rule sibling_ne_imp_sibling_in_alphabet)
    have dd: "depth u ?d = height u" using dc cu by simp

    let ?u' = "swapFourSyms u a b c ?d"
    have cu': "consistent ?u'" using cu by simp
    have au': "alphabet ?u' = alphabet u" using aa ab ac ad au by simp
    have fu': "freq ?u' = freq u" using aa ab ac ad cu fu by simp
    have sa: "sibling ?u' a = b" using cu aa ab ac ab dc
      by (rule sibling_swapFourSyms_when_4th_is_sibling)

    let ?v = "mergeSibling ?u' a"
    have cv: "consistent ?v" using cu' by simp
    have av: "alphabet ?v = alphabet t" using sa cu' au' aa au assms by auto
    have fv: "freq ?v = freq t"
      using sa cu' au' fu' fu [THEN sym] ab au [THEN sym] assms
      by (simp add: freq_mergeSibling ext)

    have "cost ?t' = cost t + wa + wb" using assms by simp
    also have "\<dots> \<le> cost ?v + wa + wb" using cv av fv `optimum t`
      by (simp add: optimum_def)
    also have "\<dots> = cost ?u'"
      proof -
        have "cost ?v + freq ?u' a + freq ?u' (sibling ?u' a) = cost ?u'"
          using cu' sa assms by (subst cost_mergeSibling) auto
        moreover have "wa = freq ?u' a" "wb = freq ?u' b"
          using fu' fu [THEN sym] assms by clarsimp+
        ultimately show ?thesis using sa by simp
      qed
    also have "\<dots> \<le> cost u"
      proof -
        have "minima u a b" using au fu assms
          by (subst twice_freq_le_imp_minima) auto
        with cu show ?thesis using ac ad dc dd dc [THEN not_sym]
          by (rule cost_swapFourSyms_le)
      qed
    finally show ?thesis .
  qed
qed

lemma cachedWeight_splitLeaf [simp]:
"cachedWeight (splitLeaf t wa a wb b) = cachedWeight t"
by (case_tac t) simp+

lemma splitLeafF_insortTree_when_in_alphabet_left [simp]:
"\<lbrakk>alphabet t a; consistent t; a \<notin> alphabetF ts; freq t a = wa + wb\<rbrakk> \<Longrightarrow>
 splitLeafF (insortTree t ts) wa a wb b = insortTree (splitLeaf t wa a wb b) ts"
by (induct ts) simp+

lemma splitLeafF_insortTree_when_in_alphabetF_tail [simp]:
"\<lbrakk>a \<in> alphabetF ts; consistentF ts; ~ alphabet t a; freqF ts a = wa + wb\<rbrakk> \<Longrightarrow>
 splitLeafF (insortTree t ts) wa a wb b =
     insortTree t (splitLeafF ts wa a wb b)"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons u us) show ?case
  proof (cases "alphabet u a")
    case True
    moreover hence "a \<notin> alphabetF us" using Cons by auto
    ultimately show ?thesis using Cons by auto
  next
    case False thus ?thesis using Cons by simp
  qed
qed

lemma splitLeaf_huffman_commute:
"\<lbrakk>consistentF ts; ts \<noteq> []; a \<in> alphabetF ts; freqF ts a = wa + wb\<rbrakk> \<Longrightarrow>
 splitLeaf (huffman ts) wa a wb b = huffman (splitLeafF ts wa a wb b)"
proof (induct ts rule: huffman.induct)
  case 3 thus ?case by simp
next
  case (1 t) thus ?case by simp
next
  case (2 t1 t2 ts)
  note hyps = 2
  show ?case
  proof (cases "alphabet t1 a")
    case True
    moreover hence "~ alphabet t2 a" "a \<notin> alphabetF ts" using hyps by auto
    ultimately show ?thesis using hyps by (simp add: uniteTrees_def)
  next
    case False
    note a1 = False
    show ?thesis
    proof (cases "alphabet t2 a")
      case True
      moreover hence "a \<notin> alphabetF ts" using hyps by auto
      ultimately show ?thesis using a1 hyps by (simp add: uniteTrees_def)
    next
      case False
      thus ?thesis using a1 hyps by simp
    qed
  qed
qed

lemma max_0_imp_0 [simp]:
"(max x y = (0::nat)) = (x = 0 \<and> y = 0)"
by auto

fun even and odd where
  "even 0 = True"
| "odd 0 = False"
| "even (Suc n) = odd n"
| "odd (Suc n) = even n"

lemma "even m"
nunchaku[overlord]

lemma "optimum (InnerNode (Suc (Suc 0)) (Leaf (Suc 0) a) (Leaf (Suc 0) a))"
unfolding optimum_def
nxunchaku[overlord, timeout = 60]


theorem optimum_huffman:
"(* \<lbrakk>consistentF ts; (* heightF ts' = 0; *) sortedByWeight ts; ts \<noteq> []\<rbrakk> \<Longrightarrow> *)
 optimum (huffman [])"
unfolding optimum_def
apply auto
(* quickcheck *)
oops
nunchxaku[overlord, timeout = 60]
(* nunchaku[overlord] *)

proof (induct ts rule: length_induct)
  case (1 ts)
  note hyps = 1
  show ?case
  proof (cases ts)
    case Nil thus ?thesis using `ts \<noteq> []` by fast
  next
    case (Cons ta ts')
    note ts = Cons
    show ?thesis
    proof (cases ts')
      case Nil thus ?thesis using ts hyps by (simp add: optimum_def)
    next
      case (Cons tb ts'')
      note ts' = Cons
      show ?thesis
      proof (cases ta)
        case (Leaf wa a)
        note la = Leaf
        show ?thesis
        proof (cases tb)
          case (Leaf wb b)
          note lb = Leaf
          show ?thesis
          proof -
            let ?us = "insortTree (uniteTrees ta tb) ts''"
            let ?us' = "insortTree (Leaf (wa + wb) a) ts''"
            let ?ts = "splitLeaf (huffman ?us') wa a wb b"
            have e1: "huffman ts = huffman ?us" using ts' ts by simp
            have e2: "huffman ?us = ?ts" using la lb ts' ts hyps
              by (auto simp: splitLeaf_huffman_commute uniteTrees_def)

            have "optimum (huffman ?us')" using la ts' ts hyps
              by (drule_tac x = ?us' in spec)
                 (auto dest: sortedByWeight_Cons_imp_sortedByWeight
                       simp: sortedByWeight_insortTree)
            hence "optimum ?ts" using la lb ts' ts hyps
              apply simp
              apply (rule optimum_splitLeaf)
              by (auto dest!: heightF_0_imp_Leaf_freqF_in_set
                              sortedByWeight_Cons_imp_forall_weight_ge)
            thus "optimum (huffman ts)" using e1 e2 by simp
          qed
        next
          case InnerNode thus ?thesis using ts' ts hyps by simp
        qed
      next
        case InnerNode thus ?thesis using ts' ts hyps by simp
      qed
    qed
  qed
qed

end
