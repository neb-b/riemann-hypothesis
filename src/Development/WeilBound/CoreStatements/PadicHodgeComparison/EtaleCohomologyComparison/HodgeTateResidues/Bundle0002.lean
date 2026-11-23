module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.RedPullPd
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

universe u v w

namespace CrystallineSemistableComparison.HT

open PAlg

section Gen
variable {O : Type} [CommRing O] {F : B.Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem pd_pull_eq {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {σ : Λ →+* Λ'} {C' : Type u} [Category.{v} C']
    {F' : C' ⥤ ModuleCat.{w} Λ'} {r : ℕ} (m m' : CH.Mor (B.pdS (F.cr b ht κ) c r).fn F' σ) (η : ∀ T, m.G.obj T ⟶ m'.G.obj T)
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (m.G.obj T).B), (η T').φ ((m.G.map f).φ x) = (m'.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') (x : (m.G.obj T).B) hx hx', m'.τ T ⟨(η T).φ x, hx'⟩ = m.τ T ⟨x, hx⟩) (n : ℕ)
    (x : CH.H (B.pdS (F.cr b ht κ) c r).fn n) : m.pull n x = m'.pull n x :=
  CrystallineSemistableComparison.P.prism m m' ⟨η, fun _ _ f => Thick.Hom.ext (RingHom.ext (nat f)) (funext fun j => j.elim)⟩
    (fun T x => hτ T x.1 x.2 _) n x

end Gen

theorem pd_square {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1} {h₃ : b₃.t = 1}
    {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I} {κ₄ : O →+* b₄.R ⧸ b₄.I}
    {Λ : Type} [CommRing Λ] {c₁ : Λ →+* b₁.R} {c₂ : Λ →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τ : Λ →+* Λ}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τ a)) (hb : ∀ a, σb (c₂ a) = c₄ (RingHom.id Λ a)) (hc : ∀ a, σc (c₁ a) = c₃ (RingHom.id Λ a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τ a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (r j : ℕ) (x : CH.H (B.pdS (F₁.cr b₁ h₁ κ₁) c₁ r).fn j) :
    (pdOm (c := c₂) (c' := c₄) mb (RingHom.id Λ) hb r).pull j ((pdOm (c := c₁) (c' := c₂) ma τ ha r).pull j x) =
      (pdOm (c := c₃) (c' := c₄) md τ hd r).pull j ((pdOm (c := c₁) (c' := c₃) mc (RingHom.id Λ) hc r).pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact pd_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) j x

theorem pd_id {O : Type} [CommRing O] {F : B.Fn O} {b : Base} {h : b.t = 1} {κ : O →+* b.R ⧸ b.I} {Λ : Type} [CommRing Λ]
    {c : Λ →+* b.R} {σ : b.R →+* b.R} (m : Mor (F.cr b h κ) (F.cr b h κ) σ) (hc : ∀ a, σ (c a) = c (RingHom.id Λ a))
    (hσ : ∀ r, σ r = r) (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F.cr b h κ).Pt.obj B₀), (m.pt.app B₀ y).1.2 = y.1.2)
    (r j : ℕ) (x : CH.H (B.pdS (F.cr b h κ) c r).fn j) : (pdOm (c := c) (c' := c) m (RingHom.id Λ) hc r).pull j x = x :=
  (pd_pull_eq (pdOm (c := c) (c' := c) m (RingHom.id Λ) hc r) (CH.Mor.id _)
    (fun T => crHom (T := m.obj T) (T' := T) (RingHom.id T.B) (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism
      fun h => (pt_id _ h _).trans (hpt _ _)) (fun _ _ => rfl) (fun _ _ _ _ => rfl) j x).trans
    (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id Λ) (CH.Mor.id _) (CH.Mor.id _) j x).2

theorem pd_om_sh {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : Mor L L' σ) {Λ : Type} [CommRing Λ]
    {c : Λ →+* b.R} {c' : Λ →+* b'.R} (h : ∀ a, σ (c a) = c' (RingHom.id Λ a)) {t : Λ} (h1 : c t ∈ b.I) (h2 : c' t ∈ b'.I)
    {r r' : ℕ} (k : ℕ) (e : r + k = r') (j : ℕ) (x : CH.H (B.pdS L c r).fn j) :
    (pdOm (c := c) (c' := c') m (RingHom.id Λ) h r').pull j ((pdSh L c h1 k e).pull j x) =
      (pdSh L' c' h2 k e).pull j ((pdOm (c := c) (c' := c') m (RingHom.id Λ) h r).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  exact congrArg (fun u => (s.obj (Fin.last j)).i u *
    (show (s.obj (Fin.last j)).B from (show (B.pdS L c r).S _ from z.1 (s ⋙ m.functor)).1)) (h (t ^ k))

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem red_gal_pd (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (r n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false (n + 1)) ((base l).cris (n + 1)) r).fn j) :
    (pdOm (CrystallineSemistableComparison.SH.redM F κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false (n + 1)) (ACris.galCris σ) (galBase_cris σ (n + 1)) r).pull j x) =
      (pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.redM F κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j x) :=
  pd_square (CrystallineSemistableComparison.SH.galM F κ σ hσ false (n + 1)) (CrystallineSemistableComparison.SH.redM F κ false n) (CrystallineSemistableComparison.SH.redM F κ false n)
    (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (galBase_cris σ (n + 1)) (B.red_cris _ n.le_succ) (B.red_cris _ n.le_succ) (galBase_cris σ n)
    (CrystallineSemistableComparison.SH.red_galBase σ n)
    (CrystallineSemistableComparison.SH.base_base F (B.gal_κb κ σ hσ false (n + 1)) (B.red_κb κ false n.le_succ) (B.red_κb κ false n.le_succ)
      (B.gal_κb κ σ hσ false n)) r j x

variable {F} {F' : B.Fn O}

theorem red_pull_pd (u : B.Fn.Map F F') (r n j : ℕ) (x : CH.H (B.pdS (B.Lc F' κ false (n + 1)) ((base l).cris (n + 1)) r).fn j) :
    (pdOm (CrystallineSemistableComparison.SH.redM F κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.pullM κ u false (n + 1)) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j x) =
      (pdOm (CrystallineSemistableComparison.SH.pullM κ u false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j
        ((pdOm (CrystallineSemistableComparison.SH.redM F' κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) r).pull j x) :=
  pd_square (CrystallineSemistableComparison.SH.pullM κ u false (n + 1)) (CrystallineSemistableComparison.SH.redM F κ false n) (CrystallineSemistableComparison.SH.redM F' κ false n)
    (CrystallineSemistableComparison.SH.pullM κ u false n) (CrystallineSemistableComparison.SH.idc _) (B.red_cris _ n.le_succ) (B.red_cris _ n.le_succ) (CrystallineSemistableComparison.SH.idc _)
    (fun r => (CrystallineSemistableComparison.SH.idc ((base l).red n.le_succ) r).symm) (CrystallineSemistableComparison.SH.base_map u (B.red_κb κ false n.le_succ)) r j x

end F

variable {M N : Model l K} {r r' j : ℕ}

theorem comp_add {x y : Fam M r j} (hx : Comp x) (hy : Comp y) : Comp (x + y) := fun n =>
  (map_add (redS M r n j) (x (n + 1)) (y (n + 1))).trans (congrArg₂ (· + ·) (hx n) (hy n))

theorem comp_smul (c : Acris l) {x : Fam M r j} (hx : Comp x) : Comp (c • x) := fun n =>
  (map_smul (redS M r n j) c (x (n + 1))).trans (congrArg (c • ·) (hx n))

theorem comp_sh (ht : TFil l) (k : ℕ) (h : r + k = r') {x : Fam M r j} (hx : Comp x) : Comp (shS ht k h x) := fun n =>
  (pd_om_sh (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (B.red_cris _ n.le_succ) (ht (base l) (n + 1)) (ht (base l) n)
    k h j (x (n + 1))).trans (congrArg ((pdSh (M.L false n) ((base l).cris n) (ht (base l) n) k h).pull j) (hx n))

theorem comp_gal (σ : K.fixingSubgroup) {x : Fam M r j} (hx : Comp x) : Comp (galS σ x) := fun n =>
  (red_gal_pd (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) r n j (x (n + 1))).trans
    (congrArg ((pdOm (CrystallineSemistableComparison.SH.galM (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) false n)
      (ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (galBase_cris _ n) r).pull j) (hx n))

theorem comp_pull (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {x : Fam N r j} (hx : Comp x) : Comp (pullS u hu x) := fun n =>
  (red_pull_pd (okToOC l K) (B.schMap u hu) r n j (x (n + 1))).trans
    (congrArg ((pdOm (CrystallineSemistableComparison.SH.pullM (okToOC l K) (B.schMap u hu) false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j) (hx n))

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ReductionCommutesTMor
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris Formalism.Per6

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT.Red

open CH PAlg B

section Gen
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R}

theorem sub_mulSub (m : CH.Mor F F' (RingHom.id R)) (c : R) (S₁ S₂ : SubF F) (S₁' S₂' : SubF F') (h₁ h₂ k k') (j : ℕ) (x : H S₁.fn j) :
    (subMor m S₂ S₂' h₂).pull j ((mulSub c S₁ S₂ k).pull j x) = (mulSub c S₁' S₂' k').pull j ((subMor m S₁ S₁' h₁).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (map_smul (m.τ _) c _)))

theorem sub_mulTo (m : CH.Mor F F' (RingHom.id R)) (c : R) (S : SubF F) (S' : SubF F') (h k k') (j : ℕ) (x : H F j) :
    (subMor m S S' h).pull j ((mulTo c S k).pull j x) = (mulTo c S' k').pull j (m.pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (map_smul (m.τ _) c _)))

theorem mulSub_mulTo (c c' c'' : R) (e : c'' = c' * c) (S S' : SubF F) (k k' k'') (j : ℕ) (x : H F j) :
    (mulSub c' S S' k').pull j ((mulTo c S k).pull j x) = (mulTo c'' S' k'').pull j x := by
  subst e
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (mul_smul c' c _).symm))

end Gen

section Pd
variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {c' : Λ →+* b'.R} {σ : b.R →+* b'.R}

theorem om_sh (m : GlobalTheory.LogCris.Mor L L' σ) (h : ∀ a, σ (c a) = c' (RingHom.id Λ a)) {t : Λ} (ht : c t ∈ b.I) (ht' : c' t ∈ b'.I)
    {r r' : ℕ} (k : ℕ) (e : r + k = r') (j : ℕ) (x : H (pdS L c r).fn j) :
    (pdOm m (RingHom.id Λ) h r').pull j ((pdSh L c ht k e).pull j x) =
      (pdSh L' c' ht' k e).pull j ((pdOm m (RingHom.id Λ) h r).pull j x) :=
  sub_mulSub (omMor m (RingHom.id Λ) h) (t ^ k) _ _ _ _ _ _ _ _ j x

end Pd

section PdCr
variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem cr_pull_eq' {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {σ : Λ →+* Λ'} {C' : Type u} [Category.{v} C']
    {F' : C' ⥤ ModuleCat.{w} Λ'} (r : ℕ) (m m' : CH.Mor (pdS (F.cr b ht κ) c r).fn F' σ) (η : ∀ T, m.G.obj T ⟶ m'.G.obj T)
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (m.G.obj T).B), (η T').φ ((m.G.map f).φ x) = (m'.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') x, m'.τ T (((pdS (F.cr b ht κ) c r).fn.map (η T)).hom x) = m.τ T x) (n : ℕ) (x : H (pdS (F.cr b ht κ) c r).fn n) :
    m.pull n x = m'.pull n x :=
  CrystallineSemistableComparison.P.prism m m' ⟨η, fun _ _ f => Thick.Hom.ext (RingHom.ext (nat f)) (funext fun j => j.elim)⟩ hτ n x

end PdCr

theorem map_eq (P : CommRingCat.{0} ⥤ Type) {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) (h : A →+* C) (e : g.comp f = h) (y : P.obj (CommRingCat.of A)) :
    P.map (CommRingCat.ofHom g) (P.map (CommRingCat.ofHom f) y) = P.map (CommRingCat.ofHom h) y := by
  rw [← Functor.map_comp_apply, ← CommRingCat.ofHom_comp, e]

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redT (P : PAlg l ⥤ Type) (r n : ℕ) : CH.Mor (TT P r (n + 1)).fn (TT P r n).fn (RingHom.id _) :=
  subMor (CH.Mor.ofNatTrans (redEl P n.le_succ)) _ _ fun T x hx =>
    mem_TT.2 (Pb.dividedPowerFiltration_map (dd_red false T.1.obj n.le_succ) r (mem_TT.1 hx))

theorem reduction_commutes_tMor (ht : TFil l) (P : PAlg l ⥤ Type) (r n j : ℕ) (y : MH P (n + 1) j) :
    (redT P r n).pull j ((tMor ht P r (n + 1)).pull j y) = (tMor ht P r n).pull j ((MSys P j).r n y) :=
  sub_mulTo (CH.Mor.ofNatTrans (redEl P n.le_succ)) (tA l ^ r) _ _ _ _ _ j y

theorem red_uJ (k : Bool) (A : PAlg l) {m n : ℕ} (h : n ≤ m) (hle : JJ k A m ≤ (JJ k A n).comap (A.red h)) :
    (Ideal.quotientMap _ (A.red h) hle).comp (uJ k A m) = uJ k A n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem red_comm (A : PAlg l) {m n : ℕ} (h : n ≤ m) (r : (base l).Acr m) :
    A.red h (mapAcr A.fromBase m r) = mapAcr A.fromBase n ((base l).red h r) :=
  PdOk.red_acr (pdOk_hom A.fromBase) h r

def redTh (n : ℕ) (T : El (F.pt κ)) :
    (gT F κ false (n + 1)).obj T ⟶ (SH.redM F κ false n).functor.obj ((gT F κ false n).obj T) :=
  crHom (T := gObj F κ false (n + 1) ((jE _).obj T)) (T' := (SH.redM F κ false n).obj (gObj F κ false n ((jE _).obj T)))
    (T.1.obj.red n.le_succ) (red_comm T.1.obj n.le_succ) (dd_red false T.1.obj n.le_succ)
    fun h => map_eq F.Pt _ _ _ (red_uJ false T.1.obj n.le_succ h) T.2.1

theorem β_red (r n j : ℕ) (x : H (pdS (Lc F κ false (n + 1)) ((base l).cris (n + 1)) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r).pull j x) =
      (redT (F.pt κ) r n).pull j ((βMorF F κ r (n + 1)).pull j x) :=
  ((pull_pull (RingHom.id _) (pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r) (βMorF F κ r n) j x).trans
    (cr_pull_eq' r ((βMorF F κ r (n + 1)).comp (redT (F.pt κ) r n))
      ((pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) r).comp (βMorF F κ r n)) (redTh F κ n)
      (fun f x => PdOk.red_acr (pdOk_hom f.1.hom) n.le_succ x) (fun T x => rfl) j x).symm).trans
    (pull_pull (RingHom.id _) (βMorF F κ r (n + 1)) (redT (F.pt κ) r n) j x).symm

theorem tt_mul (ht : TFil l) (P : PAlg l ⥤ Type) {r r' : ℕ} (k : ℕ) (e : r + k = r') (n : ℕ) (T : El P)
    (x : (modF (AcrEl P n)).obj T) (hx : x ∈ (TT P r n).S T) : tA l ^ k • x ∈ (TT P r' n).S T := by
  have := dividedPowerFiltration_pow_mul (DD false T.1.obj n) (ht T.1.obj n) e (mem_TT.1 hx)
  rw [← map_pow] at this
  exact mem_TT.2 this

theorem β_sh (ht : TFil l) {r r' : ℕ} (k : ℕ) (e : r + k = r') (n j : ℕ) (x : H (pdS (Lc F κ false n) ((base l).cris n) r).fn j)
    (y : MH (F.pt κ) n j) (h : (βMorF F κ r n).pull j x = (tMor ht (F.pt κ) r n).pull j y) :
    (βMorF F κ r' n).pull j ((pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) k e).pull j x) =
      (tMor ht (F.pt κ) r' n).pull j y :=
  (sub_mulSub (βMor F κ false n) (tA l ^ k) _ _ _ _ _ _ _ (tt_mul ht (F.pt κ) k e n) j x).trans
    ((congrArg ((mulSub (tA l ^ k) (TT (F.pt κ) r n) (TT (F.pt κ) r' n) (tt_mul ht (F.pt κ) k e n)).pull j) h).trans
      (mulSub_mulTo (tA l ^ r) (tA l ^ k) (tA l ^ r') (by rw [← e, add_comm, pow_add]) _ _ _ _ _ j y))

end CrystallineSemistableComparison.HT.Red
end
end

