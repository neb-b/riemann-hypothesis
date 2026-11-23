module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0253
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInJAlt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.MulSubMulTo
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT

open PAlg

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

theorem sub_mulTo (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F') (h) (c : R) (hc) (c' a : R') (hc') (e : σ c = a * c')
    (j : ℕ) (y : CH.H F j) :
    (subMor m S S' h).pull j ((mulTo c S hc).pull j y) = a • (mulTo c' S' hc').pull j (m.pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ (c • z.1 (s ⋙ m.G)) = a • c' • m.τ _ (z.1 (s ⋙ m.G))
  rw [LinearMap.map_smulₛₗ, e, mul_smul]

theorem sub_mulSub (m : CH.Mor F F' σ) (S₁ S₂ : CH.SubF F) (S₁' S₂' : CH.SubF F') (h₁ h₂) (c : R) (hc) (c' : R') (hc') (e : σ c = c')
    (j : ℕ) (y : CH.H S₁.fn j) :
    (subMor m S₂ S₂' h₂).pull j ((mulSub c S₁ S₂ hc).pull j y) = (mulSub c' S₁' S₂' hc').pull j ((subMor m S₁ S₁' h₁).pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ (c • (show S₁.S _ from z.1 (s ⋙ m.G)).1) = c' • m.τ _ (show S₁.S _ from z.1 (s ⋙ m.G)).1
  rw [LinearMap.map_smulₛₗ, e]

theorem mulSub_mulTo (S S' : CH.SubF F) (c c' c'' : R) (h h' h'') (e : c' * c = c'') (j : ℕ) (y : CH.H F j) :
    (mulSub c' S S' h').pull j ((mulTo c S h).pull j y) = (mulTo c'' S' h'').pull j y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change c' • c • z.1 s = c'' • z.1 s
  rw [smul_smul, e]

theorem sub_square {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{0} R} {F₂ : C₂ ⥤ ModuleCat.{0} R} {F₃ : C₃ ⥤ ModuleCat.{0} R} {F₄ : C₄ ⥤ ModuleCat.{0} R}
    {σ₁ σ₂ σ₃ σ₄ : R →+* R} (τ : R →+* R) [RingHomCompTriple σ₁ σ₂ τ] [RingHomCompTriple σ₃ σ₄ τ]
    (m : CH.Mor F₁ F₂ σ₁) (b : CH.Mor F₂ F₃ σ₂) (b' : CH.Mor F₁ F₄ σ₃) (q : CH.Mor F₄ F₃ σ₄)
    (S₁ : CH.SubF F₁) (S₂ : CH.SubF F₂) (S₃ : CH.SubF F₃) (S₄ : CH.SubF F₄) (hm hb hb' hq)
    (η : b.G ⋙ m.G ⟶ q.G ⋙ b'.G)
    (hτ : ∀ T x, q.τ T (b'.τ (q.G.obj T) ((F₁.map (η.app T)).hom x)) = b.τ T (m.τ (b.G.obj T) x)) (n : ℕ) (x : CH.H S₁.fn n) :
    (subMor b S₂ S₃ hb).pull n ((subMor m S₁ S₂ hm).pull n x) = (subMor q S₄ S₃ hq).pull n ((subMor b' S₁ S₄ hb').pull n x) := by
  rw [pull_pull τ, pull_pull τ]
  exact CrystallineSemistableComparison.P.prism ((subMor m S₁ S₂ hm).comp (σ'' := τ) (subMor b S₂ S₃ hb))
    ((subMor b' S₁ S₄ hb').comp (σ'' := τ) (subMor q S₄ S₃ hq)) η (fun T x => Subtype.ext (hτ T x.1)) n x

end Gen

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section P
variable (ht : TFil l) (P : PAlg l ⥤ Type)

def shT {r r' : ℕ} (k : ℕ) (h : r + k = r') (n : ℕ) : CH.Mor (TT P r n).fn (TT P r' n).fn (RingHom.id _) :=
  mulSub (tA l ^ k) (TT P r n) (TT P r' n) fun T (x : T.1.obj.Acr n) hx => mem_TT.2 (by
    have := dividedPowerFiltration_pow_mul (B.DD false T.1.obj n) (ht T.1.obj n) h (mem_TT.1 hx)
    rw [← map_pow] at this
    exact this)

theorem shT_tMor {r r' : ℕ} (k : ℕ) (h : r + k = r') (n j : ℕ) (y : MH P n j) :
    (shT ht P k h n).pull j ((tMor ht P r n).pull j y) = (tMor ht P r' n).pull j y :=
  mulSub_mulTo (TT P r n) (TT P r' n) (tA l ^ r) (tA l ^ k) (tA l ^ r') _ _ _ (by rw [← pow_add, add_comm, h]) j y

variable {P}

def galT (σ : Gal(PadicAlgCl l/K)) (a : P ⟶ twF σ ⋙ P) (r n : ℕ) : CH.Mor (TT P r n).fn (TT P r n).fn (ACris.galCris σ) :=
  subMor (galMor σ a n) (TT P r n) (TT P r n) fun T x hx =>
    mem_TT.2 (Pb.dividedPowerFiltration_map (GlobalTheory.CompanionTheory.BetaGal.dd_twAcr false σ T.1.obj n) r ((mem_TT (T := (elTw σ a).obj T)).1 hx))

theorem galT_tMor (σ : Gal(PadicAlgCl l/K)) (a : P ⟶ twF σ ⋙ P) (r n j : ℕ) (y : MH P n j) :
    (galT σ a r n).pull j ((tMor ht P r n).pull j y) = χA σ ^ r • (tMor ht P r n).pull j ((galMor σ a n).pull j y) :=
  sub_mulTo (galMor σ a n) (TT P r n) (TT P r n) _ (tA l ^ r) _ (tA l ^ r) (χA σ ^ r) _
    (by rw [map_pow, galCris_tA, mul_pow]) j y

def pullT' {P' : PAlg l ⥤ Type} (u : P ⟶ P') (r n : ℕ) : CH.Mor (TT P' r n).fn (TT P r n).fn (RingHom.id _) :=
  subMor (pullMor u n) (TT P' r n) (TT P r n) fun T x hx => mem_TT.2 ((mem_TT (T := (elMap u).obj T)).1 hx)

theorem pullT_tMor {P' : PAlg l ⥤ Type} (u : P ⟶ P') (r n j : ℕ) (y : MH P' n j) :
    (pullT' u r n).pull j ((tMor ht P' r n).pull j y) = (tMor ht P r n).pull j ((pullMor u n).pull j y) :=
  (sub_mulTo (pullMor u n) (TT P' r n) (TT P r n) _ (tA l ^ r) _ (tA l ^ r) 1 _ (one_mul _).symm j y).trans (one_smul _ _)

end P

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem β_sh (ht : TFil l) {r r' : ℕ} (k : ℕ) (h : r + k = r') (n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r' n).pull j ((pdSh (B.Lc F κ false n) ((base l).cris n) (ht (base l) n) k h).pull j x) =
      (shT ht (F.pt κ) k h n).pull j ((βMorF F κ r n).pull j x) :=
  sub_mulSub (B.βMor F κ false n) (B.pdS (B.Lc F κ false n) ((base l).cris n) r) (B.pdS (B.Lc F κ false n) ((base l).cris n) r')
    (TT (F.pt κ) r n) (TT (F.pt κ) r' n) _ _ (tA l ^ k) _ (tA l ^ k) _ rfl j x

theorem β_galF (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (r n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).pull j x) =
      (galT σ (B.ptTw F κ σ hσ) r n).pull j ((βMorF F κ r n).pull j x) := by
  have h1 := pull_pull (ACris.galCris σ) (pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r)
    (βMorF F κ r n) j x
  have h2 := pull_pull (ACris.galCris σ) (βMorF F κ r n) (galT σ (B.ptTw F κ σ hσ) r n) j x
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (pd_pull_eq ((βMorF F κ r n).comp (σ'' := ACris.galCris σ) (galT σ (B.ptTw F κ σ hσ) r n))
    ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).comp (σ'' := ACris.galCris σ) (βMorF F κ r n))
    (GlobalTheory.CompanionTheory.BetaGal.etaGal F κ σ hσ false n) (fun f x => twAcr_mapAcr σ f.1.hom n x) (fun _ _ _ _ => rfl) j x).symm

variable {F} {F' : B.Fn O}

theorem β_pullF (u : B.Fn.Map F F') (r n j : ℕ) (x : CH.H (B.pdS (B.Lc F' κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (CrystallineSemistableComparison.SH.pullM κ u false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j x) =
      (pullT' (u.pt κ) r n).pull j ((βMorF F' κ r n).pull j x) :=
  sub_square (RingHom.id _) (B.pullMorC κ u false n) (B.βMor F κ false n) (B.βMor F' κ false n) (pullMor (u.pt κ) n)
    (B.pdS (B.Lc F' κ false n) ((base l).cris n) r) (B.pdS (B.Lc F κ false n) ((base l).cris n) r) (TT (F.pt κ) r n) (TT (F'.pt κ) r n)
    _ _ _ _ (GlobalTheory.CompanionTheory.BetaPull.cmpNat κ u false n) (fun _ _ => rfl) j x

end F

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.RedSubVal
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.Mul

open Pb

theorem pull_sqC {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄] {C₁ C₂ C₃ C₄ : Type 1}
    [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄] {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂}
    {F₃ : C₃ ⥤ ModuleCat.{0} R₃} {F₄ : C₄ ⥤ ModuleCat.{0} R₄} {σa : R₁ →+* R₂} {σb : R₂ →+* R₄} {σc : R₁ →+* R₃} {σd : R₃ →+* R₄}
    (a : CH.Mor F₁ F₂ σa) (b : CH.Mor F₂ F₄ σb) (c : CH.Mor F₁ F₃ σc) (d : CH.Mor F₃ F₄ σd) (n : ℕ)
    (h : ∀ f s, b.pullC n (a.pullC n f) s = d.pullC n (c.pullC n f) s) (x : CH.H F₁ n) :
    b.pull n (a.pull n x) = d.pull n (c.pull n x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => h z.1 s))

theorem pull_triC {R₁ R₂ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₄] {C₁ C₂ C₄ : Type 1}
    [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₄] {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂}
    {F₄ : C₄ ⥤ ModuleCat.{0} R₄} {σa : R₁ →+* R₂} {σb : R₂ →+* R₄} {σc : R₁ →+* R₄}
    (a : CH.Mor F₁ F₂ σa) (b : CH.Mor F₂ F₄ σb) (c : CH.Mor F₁ F₄ σc) (n : ℕ)
    (h : ∀ f s, b.pullC n (a.pullC n f) s = c.pullC n f s) (x : CH.H F₁ n) :
    b.pull n (a.pull n x) = c.pull n x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => h z.1 s))

theorem cup_smul {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
    {p q n : ℕ} (h : p + q = n) (a b : R) (x : CH.H F₁ p) (y : CH.H F₂ q) : P.cup h (a • x) (b • y) = (a * b) • P.cup h x y := by
  obtain ⟨B, hB⟩ := CrystallineSemistableComparison.P.cup_bilin P h
  rw [← hB, ← hB, map_smul, map_smul, LinearMap.smul_apply, smul_smul, mul_comm]

section SM
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R' C'}
  {σ : R →+* R'} (m : SMor Φ Φ' σ) {a₁ b₁ a₂ b₂ a₃ b₃ : IdF Φ.A} {a₁' b₁' a₂' b₂' a₃' b₃' : IdF Φ'.A}
  (h : MulOk a₁ b₁ a₂ b₂ a₃ b₃) (h' : MulOk a₁' b₁' a₂' b₂' a₃' b₃')

theorem pair_mk {A : C ⥤ CommAlgCat.{0} R} {a b a' b' a'' b'' : IdF A} (h : MulOk a b a' b' a'' b'') (T : C) (x y : A.obj T)
    (hx : x ∈ a.S T) (hy : y ∈ a'.S T) : h.pair.μ T (sqMk a b x hx) (sqMk a' b' y hy) = sqMk a'' b'' (x * y) (h.aa T hx hy) :=
  h.mul_mk x y hx hy

theorem sq_cup (h₁ : m.Le a₁ a₁') (k₁ : m.Le b₁ b₁') (h₂ : m.Le a₂ a₂') (k₂ : m.Le b₂ b₂') (h₃ : m.Le a₃ a₃') (k₃ : m.Le b₃ b₃')
    {p q n : ℕ} (e : p + q = n) (x : CH.H (sq a₁ b₁) p) (y : CH.H (sq a₂ b₂) q) :
    (m.sq h₃ k₃).pull n (h.pair.cup e x y) = h'.pair.cup e ((m.sq h₁ k₁).pull p x) ((m.sq h₂ k₂).pull q y) := by
  refine CrystallineSemistableComparison.P.cup_pull h.pair h'.pair m.G (m.sq h₁ k₁).τ (m.sq h₂ k₂).τ (m.sq h₃ k₃).τ (m.sq h₁ k₁).nat (m.sq h₂ k₂).nat
    (m.sq h₃ k₃).nat (fun T x y => ?_) e x y
  obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
  obtain ⟨y, hy, rfl⟩ := sq_surj a₂ b₂ y
  refine (congrArg ((m.sq h₃ k₃).τ T) (pair_mk h _ x y hx hy)).trans ?_
  refine Eq.trans ?_ (pair_mk h' T (m.ρ T x) (m.ρ T y) (h₁ T x hx) (h₂ T y hy)).symm
  exact Subtype.ext (congrArg (Ideal.Quotient.mk _) (map_mul (m.ρ T) x y))

theorem sqC_cup (c₁ c₂ c₃ : R') (hc : c₃ = c₁ * c₂) (h₁ : m.LeC c₁ a₁ a₁') (k₁ : m.LeC c₁ b₁ b₁') (h₂ : m.LeC c₂ a₂ a₂')
    (k₂ : m.LeC c₂ b₂ b₂') (h₃ : m.LeC c₃ a₃ a₃') (k₃ : m.LeC c₃ b₃ b₃')
    {p q n : ℕ} (e : p + q = n) (x : CH.H (sq a₁ b₁) p) (y : CH.H (sq a₂ b₂) q) :
    (m.sqC c₃ h₃ k₃).pull n (h.pair.cup e x y) = h'.pair.cup e ((m.sqC c₁ h₁ k₁).pull p x) ((m.sqC c₂ h₂ k₂).pull q y) := by
  refine CrystallineSemistableComparison.P.cup_pull h.pair h'.pair m.G (m.sqC c₁ h₁ k₁).τ (m.sqC c₂ h₂ k₂).τ (m.sqC c₃ h₃ k₃).τ (m.sqC c₁ h₁ k₁).nat
    (m.sqC c₂ h₂ k₂).nat (m.sqC c₃ h₃ k₃).nat (fun T x y => ?_) e x y
  obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
  obtain ⟨y, hy, rfl⟩ := sq_surj a₂ b₂ y
  refine (congrArg ((m.sqC c₃ h₃ k₃).τ T) (pair_mk h _ x y hx hy)).trans ?_
  refine Eq.trans ?_ (pair_mk h' T _ _ (h₁ T x hx) (h₂ T y hy)).symm
  refine Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)
  change algebraMap R' _ c₃ * m.ρ T (x * y) = _
  rw [hc, map_mul, map_mul]; ring

theorem le_cup {A : C ⥤ CommAlgCat.{0} R} {a₁ b₁ a₂ b₂ a₃ b₃ a₁' b₁' a₂' b₂' a₃' b₃' : IdF A}
    (h : MulOk a₁ b₁ a₂ b₂ a₃ b₃) (h' : MulOk a₁' b₁' a₂' b₂' a₃' b₃')
    (h₁ : ∀ T, a₁.S T ≤ a₁'.S T) (k₁ : ∀ T, b₁.S T ≤ b₁'.S T) (h₂ : ∀ T, a₂.S T ≤ a₂'.S T) (k₂ : ∀ T, b₂.S T ≤ b₂'.S T)
    (h₃ : ∀ T, a₃.S T ≤ a₃'.S T) (k₃ : ∀ T, b₃.S T ≤ b₃'.S T)
    {p q n : ℕ} (e : p + q = n) (x : CH.H (sq a₁ b₁) p) (y : CH.H (sq a₂ b₂) q) :
    (sqLe h₃ k₃).pull n (h.pair.cup e x y) = h'.pair.cup e ((sqLe h₁ k₁).pull p x) ((sqLe h₂ k₂).pull q y) := by
  refine CrystallineSemistableComparison.P.cup_pull h.pair h'.pair (𝟭 C) (sqLe h₁ k₁).τ (sqLe h₂ k₂).τ (sqLe h₃ k₃).τ (sqLe h₁ k₁).nat
    (sqLe h₂ k₂).nat (sqLe h₃ k₃).nat (fun T x y => ?_) e x y
  obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
  obtain ⟨y, hy, rfl⟩ := sq_surj a₂ b₂ y
  refine (congrArg ((sqLe h₃ k₃).τ T) (pair_mk h _ x y hx hy)).trans ?_
  exact (pair_mk h' T x y (h₁ T hx) (h₂ T hy)).symm

theorem sq_sh (c : R) (c' : R') (hc : σ c = c') (h₁ : (idS Φ).LeC c a₁ a₂) (k₁ : (idS Φ).LeC c b₁ b₂) (h₂ : m.Le a₂ a₂')
    (k₂ : m.Le b₂ b₂') (h₃ : m.Le a₁ a₁') (k₃ : m.Le b₁ b₁') (h₄ : (idS Φ').LeC c' a₁' a₂') (k₄ : (idS Φ').LeC c' b₁' b₂')
    (n : ℕ) (x : CH.H (sq a₁ b₁) n) :
    (m.sq h₂ k₂).pull n (((idS Φ).sqC c h₁ k₁).pull n x) = ((idS Φ').sqC c' h₄ k₄).pull n ((m.sq h₃ k₃).pull n x) := by
  have key : ∀ (T : C') (x : sqM a₁ b₁ (m.G.obj T)), (m.sq h₂ k₂).τ T (((idS Φ).sqC c h₁ k₁).τ (m.G.obj T) x) =
      ((idS Φ').sqC c' h₄ k₄).τ T ((m.sq h₃ k₃).τ T x) := by
    intro T x
    obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
    refine Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)
    change m.ρ T (algebraMap R _ c * x) = algebraMap R' _ c' * m.ρ T x
    rw [map_mul, m.comm, hc]
  exact pull_sqC _ _ _ _ n (fun f s => key _ (f (s ⋙ m.G))) x

theorem sqC_sh (c c' c'' : R') (hc : c'' = c' * c) (h₁ : m.LeC c a₁ a₁') (k₁ : m.LeC c b₁ b₁') (h₂ : (idS Φ').LeC c' a₁' a₂')
    (k₂ : (idS Φ').LeC c' b₁' b₂') (h₃ : m.LeC c'' a₁ a₂') (k₃ : m.LeC c'' b₁ b₂') (n : ℕ) (x : CH.H (sq a₁ b₁) n) :
    ((idS Φ').sqC c' h₂ k₂).pull n ((m.sqC c h₁ k₁).pull n x) = (m.sqC c'' h₃ k₃).pull n x := by
  have key : ∀ (T : C') (x : sqM a₁ b₁ (m.G.obj T)), ((idS Φ').sqC c' h₂ k₂).τ T ((m.sqC c h₁ k₁).τ T x) = (m.sqC c'' h₃ k₃).τ T x := by
    intro T x
    obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
    refine Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)
    change algebraMap R' _ c' * (algebraMap R' _ c * m.ρ T x) = algebraMap R' _ c'' * m.ρ T x
    rw [hc, map_mul, mul_assoc]
  exact pull_triC _ _ _ n (fun f s => key _ (f (s ⋙ m.G))) x

theorem le_sh {a₁' b₁' a₂' b₂' : IdF Φ.A} (c : R) (h₁ : (idS Φ).LeC c a₁ a₂) (k₁ : (idS Φ).LeC c b₁ b₂) (h₂ : ∀ T, a₂.S T ≤ a₂'.S T)
    (k₂ : ∀ T, b₂.S T ≤ b₂'.S T) (h₃ : ∀ T, a₁.S T ≤ a₁'.S T) (k₃ : ∀ T, b₁.S T ≤ b₁'.S T) (h₄ : (idS Φ).LeC c a₁' a₂')
    (k₄ : (idS Φ).LeC c b₁' b₂') (n : ℕ) (x : CH.H (sq a₁ b₁) n) :
    (sqLe h₂ k₂).pull n (((idS Φ).sqC c h₁ k₁).pull n x) = ((idS Φ).sqC c h₄ k₄).pull n ((sqLe h₃ k₃).pull n x) := by
  have key : ∀ (T : C) (x : sqM a₁ b₁ T), (sqLe h₂ k₂).τ T (((idS Φ).sqC c h₁ k₁).τ T x) =
      ((idS Φ).sqC c h₄ k₄).τ T ((sqLe h₃ k₃).τ T x) := by
    intro T x
    obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
    rfl
  exact pull_sqC _ _ _ _ n (fun f s => key _ (f s)) x

end SM

theorem sup_mul {B : Type} [CommRing B] {I J P N : Ideal B} (h : ∀ x ∈ I, ∀ y ∈ J, x * y ∈ P) {x y : B} (hx : x ∈ I ⊔ N)
    (hy : y ∈ J ⊔ N) : x * y ∈ P ⊔ N := by
  obtain ⟨a, ha, n, hn, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨b, hb, n', hn', rfl⟩ := Submodule.mem_sup.1 hy
  have : (a + n) * (b + n') = a * b + (a * n' + n * (b + n')) := by ring
  rw [this]
  exact Submodule.add_mem_sup (h a ha b hb) (add_mem (N.mul_mem_left _ hn') (N.mul_mem_right _ hn))

theorem mul_sup {B : Type} [CommRing B] {I P N : Ideal B} {c : B} (h : ∀ x ∈ I, c * x ∈ P) {x : B} (hx : x ∈ I ⊔ N) :
    c * x ∈ P ⊔ N := by
  obtain ⟨a, ha, n, hn, rfl⟩ := Submodule.mem_sup.1 hx
  rw [mul_add]
  exact Submodule.add_mem_sup (h a ha) (N.mul_mem_left _ hn)

section Base
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

theorem okm (c : b.R) {a a' s : ℕ} (h : a + a' = s) :
    MulOk (stdI Q (some (a : ℤ)) c) (stdI Q (some ((a : ℤ) + 1)) c) (stdI Q (some (a' : ℤ)) c) (stdI Q (some ((a' : ℤ) + 1)) c)
      (stdI Q (some (s : ℤ)) c) (stdI Q (some ((s : ℤ) + 1)) c) :=
  ⟨fun T _ _ hx hy => sup_mul (fun _ hx _ hy => (grOkQ Q h).aa T hx hy) hx hy,
    fun T _ _ hx hy => sup_mul (fun _ hx _ hy => (grOkQ Q h).ab T hx hy) hx hy,
    fun T _ _ hx hy => sup_mul (fun _ hx _ hy => (grOkQ Q h).ba T hx hy) hx hy⟩

theorem lem {t : b.R} (ht : t ∈ b.I) (c : b.R) {r r' k : ℕ} (h : r' ≤ r + k) :
    (idS (sP Q)).LeC (t ^ k) (stdI Q (some (r : ℤ)) c) (stdI Q (some (r' : ℤ)) c) :=
  fun T _ hx => mul_sup (fun _ hx => fil_mul_le ht h T.obj hx) hx

def shm {t : b.R} (ht : t ∈ b.I) (c : b.R) {r r' : ℕ} (k : ℕ) (h : r + k = r') :
    CH.Mor (sq (stdI Q (some (r : ℤ)) c) (stdI Q (some ((r : ℤ) + 1)) c)) (sq (stdI Q (some (r' : ℤ)) c) (stdI Q (some ((r' : ℤ) + 1)) c))
      (RingHom.id _) :=
  (idS (sP Q)).sqC (t ^ k) (lem Q ht c (r := r) (r' := r') (by omega)) (lem Q ht c (r := r + 1) (r' := r' + 1) (by omega))

theorem red_sh {t : b.R} (ht : t ∈ b.I) (c : b.R) {r r' : ℕ} (k : ℕ) (h : r + k = r') (j : ℕ) (z : HG Q r j) :
    redG' Q c r' j (shG Q ht k h j z) = (shm Q ht c k h).pull j (redG' Q c r j z) :=
  le_sh (Φ := sP Q) (t ^ k) _ _ _ _ _ _ _ _ j z

theorem red_cup (c : b.R) {r r' s i j : ℕ} (h : r + r' = s) (z : HG Q r i) (z' : HG Q r' j) :
    redG' Q c s (i + j) (cupG Q h z z') = (okm Q c h).pair.cup rfl (redG' Q c r i z) (redG' Q c r' j z') :=
  le_cup (grOkQ Q h) (okm Q c h) _ _ _ _ _ _ rfl z z'

def oneG : HG Q 0 0 :=
  (toSq (sFil Q ((0 : ℕ) : ℤ)) (sFil Q (((0 : ℕ) : ℤ) + 1)) fun T => T.obj.pdPow_zero).pull 0 (CH.oneH (sP Q).A)

end Base

section Red
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] {I : Ideal A} {γ : DividedPowers I}
  {R : Type} [CommRing R] {I' : Ideal R} {γ' : DividedPowers I'} {κ' : O →+* R ⧸ I'} {l n : ℕ}
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (d : RedIn γ' κ' γ l n)
  {Λ : Type} [CommRing Λ] (c : Λ →+* R) (lam : Λ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))

theorem redSub_val (r : ℕ) (T : (TS γ q l s 𝒱).FullSubcategory) (x : (B.pdS (nlFun γ' l X q κ') c r).S (redObj T.obj d T.property.1))
    (y : T.obj.B) (hy : x.1 = Ideal.Quotient.mk (lnT T.obj l n) y) :
    Subtype.val ((redSub q s 𝒱 d c lam hc r).τ T x) = Ideal.Quotient.mk _ y := by
  obtain ⟨x, hx⟩ := x
  dsimp only at hy
  subst hy
  rfl

theorem redSub_rep (r : ℕ) (T : (TS γ q l s 𝒱).FullSubcategory) (x : (B.pdS (nlFun γ' l X q κ') c r).S (redObj T.obj d T.property.1)) :
    ∃ y : T.obj.B, y ∈ T.obj.pdPow r ∧ x.1 = Ideal.Quotient.mk (lnT T.obj l n) y := by
  obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
    (dividedPowerFiltration_red T.obj.δ _ Ideal.Quotient.mk_surjective _ (redδ_dp T.obj T.property.1 n) r
      ((mem_pdS (T := redObj T.obj d T.property.1)).1 x.2))
  exact ⟨y, hy, e.symm⟩

theorem redSub_mk (r : ℕ) (T : (TS γ q l s 𝒱).FullSubcategory) (x : (B.pdS (nlFun γ' l X q κ') c r).S (redObj T.obj d T.property.1))
    (y : T.obj.B) (h : y ∈ (stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)).S T) (hy : x.1 = Ideal.Quotient.mk (lnT T.obj l n) y) :
    (redSub q s 𝒱 d c lam hc r).τ T x = sqMk _ (stdI (TS γ q l s 𝒱) (some ((r : ℤ) + 1)) ((l : A) ^ n)) y h :=
  Subtype.ext (redSub_val q s 𝒱 d c lam hc r T x y hy)

include hc in
theorem i_c (T : (TS γ q l s 𝒱).FullSubcategory) (a : Λ) :
    (redObj T.obj d T.property.1).i (c a) = Ideal.Quotient.mk (lnT T.obj l n) (T.obj.i (lam a)) := by
  change iBar T.obj l n (d.ρ (c a)) = _
  rw [hc]; rfl

theorem redSub_sh {t : Λ} (ht : c t ∈ I') (ht' : lam t ∈ I) {r r' : ℕ} (k : ℕ) (h : r + k = r') (j : ℕ)
    (x : CH.H (B.pdS (nlFun γ' l X q κ') c r).fn j) :
    (redSub q s 𝒱 d c lam hc r').pull j ((pdSh (nlFun γ' l X q κ') c ht k h).pull j x) =
      (shm (TS γ q l s 𝒱) ht' ((l : A) ^ n) k h).pull j ((redSub q s 𝒱 d c lam hc r).pull j x) := by
  have key : ∀ (T : (TS γ q l s 𝒱).FullSubcategory) (x : (B.pdS (nlFun γ' l X q κ') c r).S (redObj T.obj d T.property.1)),
      (redSub q s 𝒱 d c lam hc r').τ T ((pdSh (nlFun γ' l X q κ') c ht k h).τ (redObj T.obj d T.property.1) x) =
        (shm (TS γ q l s 𝒱) ht' ((l : A) ^ n) k h).τ T ((redSub q s 𝒱 d c lam hc r).τ T x) := by
    intro T x
    obtain ⟨y, hy, e⟩ := redSub_rep q s 𝒱 d c r T x
    rw [redSub_mk q s 𝒱 d c lam hc r T x y (Ideal.mem_sup_left hy) e]
    refine Subtype.ext ((redSub_val q s 𝒱 d c lam hc r' T _ (T.obj.i (lam t ^ k) * y) ?_).trans rfl)
    refine Eq.trans (congrArg₂ (fun a b : T.obj.B ⧸ lnT T.obj l n => a * b) (i_c q s 𝒱 d c lam hc T (t ^ k)) e) ?_
    rw [map_pow lam, map_mul]
  exact pull_sqC _ _ _ _ j (fun f s' => key _ (f (s' ⋙ redG q s d 𝒱))) x

theorem redSub_cup {r r' u i j : ℕ} (h : r + r' = u) (x : CH.H (B.pdS (nlFun γ' l X q κ') c r).fn i)
    (y : CH.H (B.pdS (nlFun γ' l X q κ') c r').fn j) :
    (redSub q s 𝒱 d c lam hc u).pull (i + j) ((pdPair (nlFun γ' l X q κ') c h).cup rfl x y) =
      (okm (TS γ q l s 𝒱) ((l : A) ^ n) h).pair.cup rfl ((redSub q s 𝒱 d c lam hc r).pull i x) ((redSub q s 𝒱 d c lam hc r').pull j y) := by
  refine CrystallineSemistableComparison.P.cup_pull (pdPair (nlFun γ' l X q κ') c h) (okm (TS γ q l s 𝒱) ((l : A) ^ n) h).pair (redG q s d 𝒱)
    (redSub q s 𝒱 d c lam hc r).τ (redSub q s 𝒱 d c lam hc r').τ (redSub q s 𝒱 d c lam hc u).τ (redSub q s 𝒱 d c lam hc r).nat
    (redSub q s 𝒱 d c lam hc r').nat (redSub q s 𝒱 d c lam hc u).nat (fun T x y => ?_) rfl x y
  obtain ⟨x', hx, e⟩ := redSub_rep q s 𝒱 d c r T x
  obtain ⟨y', hy, e'⟩ := redSub_rep q s 𝒱 d c r' T y
  refine Eq.trans ?_ (congrArg₂ (fun a b => (okm (TS γ q l s 𝒱) ((l : A) ^ n) h).pair.μ T a b)
    (redSub_mk q s 𝒱 d c lam hc r T x x' (Ideal.mem_sup_left hx) e)
    (redSub_mk q s 𝒱 d c lam hc r' T y y' (Ideal.mem_sup_left hy) e')).symm
  refine Eq.trans ?_ (pair_mk (okm (TS γ q l s 𝒱) ((l : A) ^ n) h) T x' y' _ _).symm
  refine redSub_mk q s 𝒱 d c lam hc u T _ (x' * y') _ ?_
  exact (congrArg₂ (fun a b : T.obj.B ⧸ lnT T.obj l n => a * b) e e').trans (map_mul _ _ _).symm

theorem redSub_one : (redSub q s 𝒱 d c lam hc 0).pull 0 (pdOne (nlFun γ' l X q κ') c) =
    redG' (TS γ q l s 𝒱) ((l : A) ^ n) 0 0 (oneG (TS γ q l s 𝒱)) := by
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s' => Subtype.ext ?_))
  refine (redSub_val q s 𝒱 d c lam hc 0 _ _ 1 ?_).trans rfl
  exact (one_smul Λ _).trans (map_one (Ideal.Quotient.mk (lnT (s'.obj (Fin.last 0)).obj l n))).symm

end Red

end CrystallineSemistableComparison.HT.Mul
end
end

