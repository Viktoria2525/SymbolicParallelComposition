open HolKernel Parse boolLib bossLib;
open messagesTheory;
open synceventsTheory;

val _ = new_theory "dolevyao";

    
(* Dolev-Yao predicates *)
val _ = Datatype `DYpred =
K SapicTerm_t (* Adversary can deduce term *)
| Fr SapicTerm_t (* Term is fresh *)
| Equ (SapicTerm_t # SapicTerm_t) (* both terms *)
      `;
    

      
(* Dolev-Yao deduction relation *)
val (DYdeduction_rules, DYdeduction_ind, DYdeduction_cases)
= Hol_reln
  `(∀(p:DYpred) (Pi: DYpred set). (p ∈ Pi) ==> (DYdeduction Pi p)) ∧
  (∀(n:SapicTerm_t) (Pi: DYpred set). (n = (Con (Name (PubName:NameTag_t) (str:string)))) ==> (DYdeduction Pi (K n))) ∧
(∀(k:SapicTerm_t) (m:SapicTerm_t) (Pi: DYpred set). ((DYdeduction Pi (K k)) ∧ (DYdeduction Pi (K m))) ==> (DYdeduction Pi (K (FAPP  ("Enc", (2, Public, Constructor)) [m;k])))) ∧
(∀(k:SapicTerm_t) (m:SapicTerm_t) (Pi: DYpred set). ((DYdeduction Pi (K k)) ∧ (DYdeduction Pi (K (FAPP  ("Enc", (2, Public, Constructor)) [m;k])))) ==> (DYdeduction Pi (K m))) ∧
(∀(t1:SapicTerm_t) (t2:SapicTerm_t) (Pi: DYpred set). ((DYdeduction Pi (K t1)) ∧ (DYdeduction Pi (Equ (t1,t2)))) ==> (DYdeduction Pi (K t2))) ∧
(∀(n1:SapicTerm_t) (n2:SapicTerm_t) (Pi: DYpred set). ((DYdeduction Pi (Fr n1)) ∧ (DYdeduction Pi (Equ (n1,n2)))) ==> (DYdeduction Pi (Fr n2))) 
`;


(* Dolev-Yao non-synchronous events *)        
val _ = Datatype
        `DYnsyc_event =
Silent Name_t
| Alias (Var_t # SapicTerm_t)
        `;

        
(* Dolev-Yao state *)
val _ = Datatype
        `DYstate =
ESt       (* empty state *)
`;
          
        
(* Dolev-Yao transition relation *)
val DYtranrel_def =
Define` 
      (DYtranrel (Sym,Pi,ESt) (SOME (INR (P2A Y))) (Sym',Pi',ESt) = ((Y ∉ Sym) ∧ (Pi' = Pi∪{K (TVar Y)}) ∧ (Sym = Sym'))) ∧
      (DYtranrel (Sym,Pi,ESt) (SOME (INL (Alias (X',Y')))) (Sym',Pi',ESt) = ((X' ∉ Sym) ∧ (Sym' = Sym∪{X'}) ∧ (Pi' = Pi∪{Equ((TVar X'),Y')}))) ∧
      (DYtranrel (Sym,Pi,ESt) (SOME (INR (A2P X))) (Sym',Pi',ESt) = ((K (TVar X) ∈ Pi) ∧ (Pi = Pi') ∧ (Sym = Sym'))) ∧
      (DYtranrel (Sym,Pi,ESt) (SOME (INL (Silent n))) (Sym',Pi',ESt) = ((Fr (Con n) ∉ Pi ) ∧ (Pi' = Pi∪{(Fr (Con n));(K (Con n))}) ∧ (Sym = Sym'))) ∧
      (DYtranrel (Sym,Pi,ESt) (SOME (INR (Sync_Fr n'))) (Sym',Pi',ESt) = ((Fr (Con n') ∉ Pi ) ∧ (Pi' = Pi∪{Fr (Con n')}) ∧ (Sym = Sym'))) ∧
      (DYtranrel (Sym,Pi,ESt) (NONE) (Sym',Pi',ESt) = ((Pi = Pi') ∧ (Sym = Sym')))
`;                                      


(* Dolev-Yao multi transition relation *)
Inductive DYmultranrel:
[~nil:]
  (DYmultranrel ((Sym:(Var_t -> bool)),(P:(DYpred -> bool)),ESt) ([]:(DYnsyc_event + (Name_t,Var_t) sync_event) option list) ((Sym:(Var_t -> bool)),(P:(DYpred -> bool)),ESt)) /\
[~move:]
  (
  ((DYmultranrel ((Sym:(Var_t -> bool)),(P:(DYpred -> bool)),ESt) (ev:(DYnsyc_event + (Name_t,Var_t) sync_event) option list) ((Sym'':(Var_t -> bool)),(P'':(DYpred -> bool)),ESt)) /\
   (DYtranrel ((Sym'':(Var_t -> bool)),(P'':(DYpred -> bool)),ESt) (e:(DYnsyc_event + (Name_t,Var_t) sync_event) option) ((Sym':(Var_t -> bool)),(P':(DYpred -> bool)),ESt))) ==>
  ((DYmultranrel ((Sym:(Var_t -> bool)),(P:(DYpred -> bool)),ESt) ((e::ev):(DYnsyc_event + (Name_t,Var_t) sync_event) option list) ((Sym':(Var_t -> bool)),(P':(DYpred -> bool)),ESt)))
  )
End

val DYmultranrel_single = new_axiom ("DYmultranrel_single",
                                     ``∀e Sym Sym' P P'.
                                              (DYmultranrel ((Sym:(Var_t -> bool)),(P:(DYpred -> bool)),ESt) ([e]:(DYnsyc_event + (Name_t,Var_t) sync_event) option list) ((Sym':(Var_t -> bool)),(P':(DYpred -> bool)),ESt)) =
  (DYtranrel ((Sym:(Var_t -> bool)),(P:(DYpred -> bool)),ESt) (e:(DYnsyc_event + (Name_t,Var_t) sync_event) option) ((Sym':(Var_t -> bool)),(P':(DYpred -> bool)),ESt)) ``);
                                                 
val _ = export_theory();
