theory Type_infer imports Main begin

\<comment> \<open> type inference for TLA set theory \<close>

\<comment> \<open> variables \<close>
datatype 'ty var = Var int 'ty
datatype row = Row \<comment> \<open> the annotation for row variables \<close>
datatype constructor = Cstor string

datatype ty =
  Ty_var "unit var"
| Ty_top  \<comment> \<open> the universal type \<close>
| Ty_app string "ty list"
| Ty_cases "constructor list" "row var option" \<comment> \<open> A | B | C | \<rho> \<close>

value "Ty_app ''list'' [Ty_cases [Cstor ''A'', Cstor ''B''] None]"

\<comment> \<open> does a variable occur in a type? \<close>
fun var_occurs_in_ty :: "_ var \<Rightarrow> ty \<Rightarrow> bool" where
  "var_occurs_in_ty v (Ty_var v') = (v=v')"
| "var_occurs_in_ty _ Ty_top = False"
| "var_occurs_in_ty v (Ty_app _ l) = List.list_ex (var_occurs_in_ty v) l"
| "var_occurs_in_ty _ (Ty_cases _ _) = False"

\<comment> \<open> free variables of a type \<close>
fun free_vars_ty :: "ty \<Rightarrow> unit var set" where
  "free_vars_ty (Ty_var v) = {v}"
| "free_vars_ty Ty_top = {}"
| "free_vars_ty (Ty_app _ l) =  List.foldl (\<lambda> s t. s \<union> free_vars_ty t) {} l"
| "free_vars_ty (Ty_cases _ _) = {}"

definition tyvar1 :: "unit var" where "tyvar1 = Var 1 ()"
definition tyvar2 :: "unit var" where "tyvar2 = Var 2 ()"
definition tyvar3 :: "unit var" where "tyvar3 = Var 3 ()"
definition tynat :: ty where "tynat = Ty_app ''nat'' []"
definition tylist :: ty where "tylist = Ty_app ''list'' [Ty_var tyvar1]"
definition abc :: ty where "abc = Ty_cases [Cstor ''A'', Cstor ''B'', Cstor ''C''] None"

\<comment> \<open> terms (with typed variables) \<close>

datatype "term" =
  T_var "ty var"
| T_app string "term list"

value "[1,2,3] :: int list"
value "''f'' :: string"
value "T_app ''f'' [T_var (Var 1 tynat), T_app ''a'' []]"

\<comment> \<open> substitution for types: one function for regular variables, one for row variables \<close>
record subst =
  subst_tvar :: "ty var \<Rightarrow> term option"
  subst_tyvar :: "unit var \<Rightarrow> ty option"
  subst_tyrowvars :: "row var \<Rightarrow> (constructor list * row var option) option"

definition const_none :: "'a \<Rightarrow> 'b option" where "const_none _ = None"
definition subst_empty :: subst where "subst_empty = subst.make const_none const_none const_none"

fun eval_ty :: "subst \<Rightarrow> ty \<Rightarrow> ty" where
  "eval_ty _ Ty_top = Ty_top"
| "eval_ty \<sigma> (Ty_app f l) =
    ( let l' = map (eval_ty \<sigma>) l in
      if List.member l' Ty_top
      then Ty_top (* absorbing *)
      else Ty_app f l' )"
| "eval_ty \<sigma> (Ty_var v) =
    (case (subst_tyvar \<sigma>) v of
          None \<Rightarrow> Ty_var v
        | Some t \<Rightarrow> t)"
| "eval_ty \<sigma> (Ty_cases l None) = Ty_cases l None"
| "eval_ty \<sigma> (Ty_cases l (Some \<rho>)) =
    (case (subst_tyrowvars \<sigma>) \<rho> of
      None \<Rightarrow> Ty_cases l (Some \<rho>)
    | Some (l', \<rho>') \<Rightarrow> Ty_cases (l @ l') \<rho>')"

fun eval_term :: "subst \<Rightarrow> term \<Rightarrow> term" where
  "eval_term \<sigma> (T_var v) = (case subst_tvar \<sigma> v of None \<Rightarrow> (T_var v) | Some t \<Rightarrow> t)"
| "eval_term \<sigma> (T_app f l) = T_app f (List.map (eval_term \<sigma>) l)"

\<comment> \<open> generator of fresh (free) variables \<close>

record varset =
  tyvars :: "unit var set"
  tvars :: "ty var set"
  rowvars :: "row var set"

type_synonym ('s,'a) state = "'s \<Rightarrow> ('a * 's)"

fun return :: "'a \<Rightarrow> ('s, 'a) state" where
  "return x = (\<lambda> s. (x,s))"

fun bind :: "('st,'a) state \<Rightarrow> ('a \<Rightarrow> ('st,'b) state) \<Rightarrow> ('st,'b) state" (infixr "\<bind>" 80) where
  "bind f_a f = (\<lambda> s. let (x,s') = f_a s in f x s')"

\<comment> \<open> abstract generator for fresh variables \<close>
locale var_gen =
  fixes new_tyvar :: "(varset, unit var) state"
  fixes new_tvar :: "(varset, ty var) state"
  fixes new_rowvar :: "(varset, row var) state"
  assumes is_fresh_tyvar[intro,simp]: "\<forall> s. (let (x,_) = new_tyvar s in x \<notin> tyvars s)"
  assumes is_fresh_tvar[intro,simp]: "\<forall> s. (let (x,_) = new_tvar s in x \<notin> tvars s)"
  assumes is_fresh_rowvar[intro,simp]: "\<forall> s. (let (x,_) = new_rowvar s in x \<notin> rowvars s)"

\<comment> \<open> type unification.
     It lives in the monad because it might need to allocate new row variables \<close>

fun is_bound :: "unit var \<Rightarrow> subst \<Rightarrow> bool" (infix "\<in>?" 90) where
  "is_bound v \<sigma> = (case subst_tyvar \<sigma> v of Some _ \<Rightarrow> True | None \<Rightarrow> False)"

fun occur_check_ty :: "subst \<Rightarrow> unit var \<Rightarrow> ty \<Rightarrow> bool" where
  "occur_check_ty \<sigma> v ty = (v \<in> free_vars_ty (eval_ty \<sigma> ty))"

value "\<not> tyvar1 \<in>? x"

fun bind_tyvar :: "unit var \<Rightarrow> ty \<Rightarrow> subst \<Rightarrow> subst" where
  "bind_tyvar v ty \<sigma> = (\<sigma>\<lparr> subst_tyvar := (subst_tyvar \<sigma>)(v := Some ty) \<rparr>)"

fun get_tyvar :: "subst \<Rightarrow> unit var \<Rightarrow> ty" where
  "get_tyvar \<sigma> v = the (subst_tyvar \<sigma> v)"

\<comment> \<open> handle set of cases \<close>
record split_cases_rec =
  common :: "constructor set"
  left_only :: "constructor set"
  right_only :: "constructor set"

\<comment> \<open> split two cases lists l1, l2 into a common part, a left-only part, a right only part \<close>
fun split_cases :: "constructor list \<Rightarrow> constructor list \<Rightarrow> split_cases_rec" where
  "split_cases [] [] = split_cases_rec.make {} {} {}"
| "split_cases [] (c#l) = (
    let r = split_cases [] l in
    if c \<in> left_only r
      then r\<lparr> left_only := Set.remove c (left_only r),
              common := Set.insert c (common r) \<rparr>
      else r\<lparr> right_only := Set.insert c (right_only r) \<rparr> )"
| "split_cases (c#l) l2 =  (
    let r = split_cases l l2 in
    if c \<in> right_only r
      then r\<lparr> right_only := Set.remove c (right_only r),
              common := Set.insert c (common r) \<rparr>
      else r\<lparr> left_only := Set.insert c (left_only r) \<rparr> )"


\<comment> \<open> Type unification, defined inductively.
    TODO: represent, in the type, that the result can become Top?
      Or really implement this as a function (subst => ty => ty => (subst | top))
    \<close>
inductive
    unif_ty :: "subst \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> subst \<Rightarrow> bool"
and unif_ty_list :: "subst \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> subst \<Rightarrow> bool"
and unif_ty_row :: "subst \<Rightarrow> row var option \<Rightarrow> constructor set \<Rightarrow> subst \<Rightarrow> bool"
where
  left_var: "
    \<not> v1 \<in>? \<sigma> \<Longrightarrow>
    \<not> occur_check_ty \<sigma> v1 ty2 \<Longrightarrow>
    unif_ty \<sigma> (Ty_var v1) ty2 (bind_tyvar v1 ty2 \<sigma>)"
| right_var: "
    \<not> v2 \<in>? \<sigma> \<Longrightarrow>
    \<not> occur_check_ty \<sigma> v2 ty1 \<Longrightarrow>
    unif_ty \<sigma> ty1 (Ty_var v2) (bind_tyvar v2 ty1 \<sigma>)"
| deref_left: "
    v1 \<in>? \<sigma> \<Longrightarrow>
    unif_ty \<sigma> (get_tyvar \<sigma> v1) ty2 \<sigma>' \<Longrightarrow>
    unif_ty \<sigma> (Ty_var v1) ty2 \<sigma>'"
| deref_right: "
    v2 \<in>? \<sigma> \<Longrightarrow>
    unif_ty \<sigma> ty1 (get_tyvar \<sigma> v2) \<sigma>' \<Longrightarrow>
    unif_ty \<sigma> ty1 (Ty_var v2) \<sigma>'"
| same_fun: "
    f = f \<Longrightarrow>
    List.length l1 = List.length l2 \<Longrightarrow>
    unif_ty_list \<sigma> l1 l2 \<sigma>' \<Longrightarrow>
    unif_ty \<sigma> (Ty_app f l1) (Ty_app f l2) \<sigma>' "
| trivial_top: "unif_ty \<sigma> Ty_top Ty_top \<sigma>"
| cases: "
    unify_ty_row \<sigma> \<rho>1 ronly \<sigma>' \<Longrightarrow>
    unify_ty_row \<sigma>' \<rho>2 lonly \<sigma>'' \<Longrightarrow>
    split_cases l1 l2 = split_cases_rec\<lparr> left_only := lonly, right_only := ronly \<rparr> \<Longrightarrow>
    unify_ty \<sigma> (Ty_cases l1 \<rho>1) (Ty_cases l2 \<rho>2) \<sigma>'' "
| row_empty: "unify_ty_row \<sigma> None {} \<sigma>"
\<comment> \<open> TODO: introduce new row var? \<close>
| nil: "unif_ty_list \<sigma> [] [] \<sigma>"
| cons: "
    unif_ty \<sigma> x1 x2 \<sigma>' \<Longrightarrow>
    unif_ty_list \<sigma>' l1 l2 \<sigma>'' \<Longrightarrow>
    unif_ty_list \<sigma> (x1#l1) (x2#l2) \<sigma>''"

lemma test_unif1: "\<forall> ty. \<exists>\<sigma>. unif_ty subst_empty ty ty \<sigma>"
  nitpick




end