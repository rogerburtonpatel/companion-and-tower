Require Import Utf8.
Require Import lattice.
Require Import progress.
Open Scope lattice. 

Notation L_lift L := ([L ⇒ L] * [L ⇒ L])%type.

Definition p_comp {X : Type} {CL : CompleteLattice X} (f g : L_lift X) :=
  (fst f ° fst g, snd f ° snd g).

Notation "f • g" := (p_comp f g) (at level 50).

Definition p_id {L : Type} {LC : LatticeCore L} : L_lift L := (mf_id, mf_id).

(* ========================================================================= *)
Section BasicEvolution.
Context {L : Type} {LC : LatticeCore L} {LL : Lattice L}.

Variable p : L → L → Prop.
Variable b : L → L → Prop.

Notation "R '↣ₚ' S" := (p R S) (at level 70).
Notation "R '↣ₐ' S" := (b R S) (at level 70).

Context {PP : Progress p} {PB : Progress b}.

Record evolution (f g : [L ⇒ L]) : Prop :=
  { evolve : ∀ R S, R ↣ₚ S → f R ↣ₚ g S }.

Record r_evolution (f g : [L ⇒ L]) : Prop :=
  { r_evolve : ∀ R S, R ↣ₚ R → R ↣ₐ S → f R ↣ₐ g S }.

Global Instance Progress_evolution : Progress evolution.
Proof.
split.
+ firstorder.
+ intros f g h Hgh Hfg; split; intros; rewrite <- Hgh; firstorder.
+ intros A g Hg; split; intros R S HRS.
  apply progress_limit_l; intros Q [ f [ H Heq ] ]; subst.
  apply Hg; assumption.
Qed.

Global Instance Progress_r_evolution : Progress r_evolution.
Proof.
split.
+ firstorder.
+ intros f g h Hgh Hfg; split; intros; rewrite <- Hgh; firstorder.
+ intros A g Hg; split; intros R S HR HRS.
  apply progress_limit_l; intros Q [ f [ H Heq ] ]; subst.
  apply Hg; assumption.
Qed.

Lemma evolution_comp f₁ f₂ g₁ g₂ :
  evolution f₁ g₁ → evolution f₂ g₂ → evolution (f₁ ∘ f₂) (g₁ ∘ g₂).
Proof.
intros H₁ H₂; split; intros; apply H₁; apply H₂; assumption.
Qed.

Lemma r_evolution_comp f₁ f₂ g₁ g₂ :
  r_evolution f₁ g₁ → evolution f₂ f₂ → r_evolution f₂ g₂ →
    r_evolution (f₁ ∘ f₂) (g₁ ∘ g₂).
Proof.
intros H₁ Hf H₂; split; intros; apply H₁.
+ apply Hf; assumption.
+ apply H₂; assumption.
Qed.

End BasicEvolution.

Notation "f '↝[' p ']' g" := (evolution p f g) (at level 70).
Notation "f '↝[' p '#' b ']' g" := (r_evolution p b f g) (at level 70).

(* ========================================================================= *)
Section Evolution.
Context {L : Type} {LC : LatticeCore L} {LL : Lattice L}.

Variable p : L → L → Prop.
Variable b : L → L → Prop.

Context {PP : Progress p} {PB : Progress b}.

Notation "R '↣ₚ' S" := (p R S) (at level 70).
Notation "R '↣ₐ' S" := (b R S) (at level 70).

Record p_evolution (f g : L_lift L) : Prop :=
  { pev_strong : fst f ↝[p] fst g
  ; pev_weak   : snd f ↝[p] snd g
  }.

Record a_evolution (f g : L_lift L) : Prop :=
  { aev_strong : fst f ↝[b] snd g
  ; aev_weak   : snd f ↝[p # b] snd g
  }.

Notation "f ↝ₚ g" := (p_evolution f g) (at level 70).
Notation "f ↝ₐ g" := (a_evolution f g) (at level 70).

Global Instance Progress_p_evolution : Progress p_evolution.
Proof.
split.
+ firstorder.
+ intros f g h Hgh Hfg; split; rewrite <- Hgh; apply Hfg.
+ intros A g Hg; split; apply progress_limit_l.
  - intros f [ h HA ]; apply Hg in HA; apply HA.
  - intros f [ h HA ]; apply Hg in HA; apply HA.
Qed.

Global Instance Progress_a_evolution : Progress a_evolution.
Proof.
split.
+ firstorder.
+ intros f g h Hgh Hfg; split; rewrite <- Hgh; apply Hfg.
+ intros A g Hg; split; apply progress_limit_l.
  - intros f [ h HA ]; apply Hg in HA; apply HA.
  - intros f [ h HA ]; apply Hg in HA; apply HA.
Qed.

Lemma p_evolution_comp f₁ f₂ g₁ g₂ :
  f₁ ↝ₚ g₁ → f₂ ↝ₚ g₂ → f₁ • f₂ ↝ₚ g₁ • g₂.
Proof.
intros H₁ H₂; split; apply evolution_comp; firstorder.
Qed.

Lemma a_evolution_comp f₁ f₂ g₁ g₂ :
  f₁ ↝ₐ g₁ → f₂ ↝ₚ f₂ → f₂ ↝ₐ g₂ → f₁ • f₂ ↝ₐ g₁ • g₂.
Proof.
intros H Hp Ha; split; simpl.
+ apply evolution_comp; firstorder.
+ apply r_evolution_comp; firstorder.
Qed.

End Evolution.