module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumMemLoc
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0010
public import GroundTheory.FunctionField.DivisorDegree
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GermCompOneAssocOfConstantCoeffZero
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPtSeqLin

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeKernelLocallyFree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_dotDual_iff (R : Subalgebra o Ω) {m : ℕ} {L : AddSubgroup (Fin m → Ω)}
    {v : Fin m → Ω} : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

theorem std_le_dual (R : Subalgebra o Ω) {m : ℕ} {A : AddSubgroup (Fin m → Ω)}
    (h : A ≤ stdLat R (Fin m)) : stdLat R (Fin m) ≤ dotDual R A := by
  intro v hv
  rw [mem_dotDual_iff]
  intro l hl
  have hl' := (LatticeGoodness.mem_stdLat R).1 (h hl)
  have hv' := (LatticeGoodness.mem_stdLat R).1 hv
  show ∑ i, l i * v i ∈ R
  exact sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)

theorem smul_mem_std (R : Subalgebra o Ω) {m : ℕ} {A : AddSubgroup (Fin m → Ω)} {w : Ω}
    (h : mulLat w (stdLat R (Fin m)) ≤ A) {v : Fin m → Ω} (hv : v ∈ dotDual R A) :
    w • v ∈ stdLat R (Fin m) := by
  classical
  rw [LatticeGoodness.mem_stdLat]
  intro j
  have h0 : (Pi.single j 1 : Fin m → Ω) ∈ stdLat R (Fin m) := by
    rw [LatticeGoodness.mem_stdLat]
    intro k
    by_cases hk : k = j
    · subst hk; simpa using R.one_mem
    · simpa [Pi.single_apply, hk] using R.zero_mem
  have h1 : w • (Pi.single j 1 : Fin m → Ω) ∈ A := h (AddSubgroup.mem_map.2 ⟨_, h0, rfl⟩)
  have h2 := (mem_dotDual_iff R).1 hv _ h1
  simpa [smul_dotProduct] using h2

theorem core (R : Subalgebra o Ω) {a b c : ℕ} (W : AddSubgroup (Fin a → Ω))
    (O : AddSubgroup (Fin c → Ω)) (Gam : AddSubgroup ((Fin a → Ω) × (Fin b → Ω)))
    (Del : AddSubgroup ((Fin b → Ω) × (Fin c → Ω))) (H : AddSubgroup (Fin b → Ω)) (w : Ω)
    (hw0 : w ≠ 0) (fW : LocFree R a W) (fO : LocFree R c O) (fH : LocFree R b H)
    (hstd : stdLat R (Fin b) ≤ H) (hwv : ∀ v ∈ H, w • v ∈ stdLat R (Fin b))
    (fIm : LocFree R c ((Del ⊓ H.prod ⊤).map (AddMonoidHom.snd _ _)))
    (sG : ∀ x ∈ R, ∀ v ∈ Gam, x • v ∈ Gam) (sD : ∀ x ∈ R, ∀ v ∈ Del, x • v ∈ Del)
    (g1 : ∀ x, (∃ y, (x, y) ∈ Gam) ↔ w • x ∈ W) (g2 : ∀ y, (0, y) ∈ Gam ↔ y ∈ stdLat R _)
    (g3 : ∀ x, (x, 0) ∈ Gam ↔ x ∈ W)
    (d1 : ∀ y, (∃ z, (y, z) ∈ Del) ↔ w • y ∈ stdLat R _) (d3 : ∀ z, (0, z) ∈ Del ↔ z ∈ O)
    (d4 : ∀ y, (y, 0) ∈ Del ↔ ∃ x, (x, y) ∈ Gam) :
    LocFree R a ((Gam ⊓ (⊤ : AddSubgroup _).prod H).map (AddMonoidHom.fst _ _)) := by

  have hK : LocFree R b ((Del ⊓ H.prod ⊤).comap (AddMonoidHom.inl _ _)) := by
    refine (LocFreeSchanuel.main R b c H _ O (Del ⊓ H.prod ⊤) fH fIm fO ?_ ?_ ?_ ?_ ?_).2
    · intro x hx v hv
      obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hv
      refine AddSubgroup.mem_inf.2 ⟨sD x hx v h1, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩
      exact fH.1 x hx _ (AddSubgroup.mem_prod.1 h2).1
    · intro v z h
      exact ⟨(AddSubgroup.mem_prod.1 (AddSubgroup.mem_inf.1 h).2).1, AddSubgroup.mem_map.2 ⟨(v, z), h, rfl⟩⟩
    · intro v hv
      obtain ⟨z, hz⟩ := (d1 v).2 (hwv v hv)
      exact ⟨z, AddSubgroup.mem_inf.2 ⟨hz, AddSubgroup.mem_prod.2 ⟨hv, trivial⟩⟩⟩
    · intro z
      constructor
      · intro h
        exact (d3 z).1 (AddSubgroup.mem_inf.1 h).1
      · intro h
        exact AddSubgroup.mem_inf.2 ⟨(d3 z).2 h, AddSubgroup.mem_prod.2 ⟨H.zero_mem, trivial⟩⟩
    · intro z hz
      obtain ⟨⟨v, z'⟩, h, rfl⟩ := AddSubgroup.mem_map.1 hz
      exact ⟨v, h⟩
  have sG' : ∀ x ∈ R, ∀ v ∈ Gam ⊓ (⊤ : AddSubgroup _).prod H, x • v ∈ Gam ⊓ (⊤ : AddSubgroup _).prod H := by
    intro x hx v hv
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hv
    exact AddSubgroup.mem_inf.2 ⟨sG x hx v h1, AddSubgroup.mem_prod.2
      ⟨trivial, fH.1 x hx _ (AddSubgroup.mem_prod.1 h2).2⟩⟩

  have hG' : LocFree R (a + b) (Gam ⊓ (⊤ : AddSubgroup _).prod H) := by
    have e1 : (Gam ⊓ (⊤ : AddSubgroup _).prod H).comap
        (LinearMap.inl Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = W := by
      ext x
      constructor
      · intro h
        exact (g3 x).1 (AddSubgroup.mem_inf.1 h).1
      · intro h
        exact AddSubgroup.mem_inf.2 ⟨(g3 x).2 h, AddSubgroup.mem_prod.2 ⟨trivial, H.zero_mem⟩⟩
    have e2 : (Gam ⊓ (⊤ : AddSubgroup _).prod H).map
        (LinearMap.snd Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom =
        (Del ⊓ H.prod ⊤).comap (AddMonoidHom.inl _ _) := by
      ext y
      constructor
      · intro h
        obtain ⟨⟨x, y'⟩, hxy, rfl⟩ := AddSubgroup.mem_map.1 h
        obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hxy
        exact AddSubgroup.mem_inf.2 ⟨(d4 y').2 ⟨x, h1⟩,
          AddSubgroup.mem_prod.2 ⟨(AddSubgroup.mem_prod.1 h2).2, trivial⟩⟩
      · intro h
        obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 h
        obtain ⟨x, hx⟩ := (d4 y).1 h1
        exact AddSubgroup.mem_map.2 ⟨(x, y), AddSubgroup.mem_inf.2 ⟨hx,
          AddSubgroup.mem_prod.2 ⟨trivial, (AddSubgroup.mem_prod.1 h2).1⟩⟩, rfl⟩
    exact LocFreeExt.main R (LinearMap.inl Ω _ _) (LinearMap.snd Ω _ _) LinearMap.inl_injective
      LinearMap.snd_surjective (LinearMap.range_inl Ω _ _) _ a b sG' (e1 ▸ fW) (e2 ▸ hK)

  have eF : Gam.map (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = divLat w W := by
    ext x
    constructor
    · intro h
      obtain ⟨⟨x', y⟩, hxy, rfl⟩ := AddSubgroup.mem_map.1 h
      exact (g1 x').1 ⟨y, hxy⟩
    · intro h
      obtain ⟨y, hy⟩ := (g1 x).2 h
      exact AddSubgroup.mem_map.2 ⟨(x, y), hy, rfl⟩
  have fDiv : LocFree R a (Gam.map (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom) :=
    eF ▸ LatticeGoodness.locFree_divLat R hw0 fW
  have hGam : LocFree R (b + a) Gam := by
    have e1 : Gam.comap (LinearMap.inr Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = stdLat R (Fin b) := by
      ext y
      exact g2 y
    exact LocFreeExt.main R (LinearMap.inr Ω _ _) (LinearMap.fst Ω _ _) LinearMap.inr_injective
      LinearMap.fst_surjective (LinearMap.range_inr Ω _ _) _ b a sG
      (e1 ▸ LatticeGoodness.locFree_stdLat R b) fDiv

  have hfin : Module.finrank Ω (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω))) = b := by
    rw [← LinearMap.range_inr, LinearMap.finrank_range_of_inj LinearMap.inr_injective,
      Module.finrank_fin_fun]
  obtain ⟨ρ, hρ1, hρ2, hρ3⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot R (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)))
    (b + a) a Gam hGam).1
    ((LatticeGoodness.locFree_map_mkQ_iff R _ LinearMap.fst_surjective Gam).2 fDiv)
  have hS : Summand (Gam ⊓ (⊤ : AddSubgroup _).prod H)
      (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω))) := by
    refine ⟨ρ, hρ1, hρ2, fun v hv => ?_⟩
    have h1 := hρ3 v (AddSubgroup.mem_inf.1 hv).1
    have h2 : (ρ v).1 = 0 := hρ1 v
    refine AddSubgroup.mem_inf.2 ⟨h1, AddSubgroup.mem_prod.2 ⟨trivial, hstd ?_⟩⟩
    apply (g2 _).1
    have : ((0 : Fin a → Ω), (ρ v).2) = ρ v := by rw [← h2]
    rwa [this]
  have hfinal := ((_root_.GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot R (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)))
    (a + b) a _ hG').2 hS).2
  rw [hfin, Nat.add_sub_cancel] at hfinal
  exact (LatticeGoodness.locFree_map_mkQ_iff R _ LinearMap.fst_surjective _).1 hfinal

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ τ, LocFree R (r τ) (D.kerH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hC hB hG₁ hG₂ hw τ
  have hw0 : w ≠ 0 := by
    obtain ⟨c, -, hc⟩ := hC.2.2.1
    intro h
    apply hC.1
    rw [hc, h, mul_zero]
  obtain ⟨-, fH, hle, -⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main D R p w χ hC hB hG₁).1 τ
  obtain ⟨-, fW, -, fO⟩ := hB.free τ
  obtain ⟨g1, g2, g3⟩ := hB.gam τ
  obtain ⟨d1, -, d3, d4⟩ := hB.del τ
  exact core R (D.W τ) (D.omHT τ) (D.Gam τ) (D.Del τ) (D.hh R p (χ τ)) w hw0 fW fO fH
    (std_le_dual R hle) (fun v hv => smul_mem_std R (hw τ) hv) (hG₂.im τ)
    (fun x hx => (hB.stable τ x hx).1) (fun x hx => (hB.stable τ x hx).2.1) g1 g2 g3 d1 d3 d4

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUnique
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullPreserve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

section Closure

variable {O Ω V : Type} [CommRing O] [Field Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V]

theorem const_smul_mem (R : Subalgebra O Ω) (A : AddSubgroup V) (c : O) {v : V}
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}) :
    algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, e, he, rfl⟩ := hw
    exact AddSubgroup.subset_closure
      ⟨algebraMap O Ω c * a, mul_mem (R.algebraMap_mem c) ha, e, he, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add w₁ w₂ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
  | neg w _ h => rw [smul_neg]; exact neg_mem h

theorem exists_const_smul_mem [IsDomain O] (R : Subalgebra O Ω) (A B : AddSubgroup V)
    (h : ∀ v ∈ A, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ B) {v : V}
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}) :
    ∃ c : O, c ≠ 0 ∧
      algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ B, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, e, he, rfl⟩ := hw
    obtain ⟨c, hc, hce⟩ := h e he
    exact ⟨c, hc, AddSubgroup.subset_closure ⟨a, ha, _, hce, smul_comm _ _ _⟩⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, hc₁, m₁⟩ := h₁
    obtain ⟨c₂, hc₂, m₂⟩ := h₂
    refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
    have e : algebraMap O Ω (c₁ * c₂) • (w₁ + w₂) =
        algebraMap O Ω c₂ • (algebraMap O Ω c₁ • w₁) +
          algebraMap O Ω c₁ • (algebraMap O Ω c₂ • w₂) := by
      rw [map_mul, smul_add, smul_smul, smul_smul, mul_comm]
    rw [e]
    exact add_mem (const_smul_mem R B c₂ m₁) (const_smul_mem R B c₁ m₂)
  | neg w _ h =>
    obtain ⟨c, hc, m⟩ := h
    exact ⟨c, hc, by rw [smul_neg]; exact neg_mem m⟩

theorem mem_span_scaled (R : Subalgebra O Ω) (A B : AddSubgroup V) (c : Ω)
    (h : ∀ v, v ∈ B ↔ ∃ e ∈ A, v = c • e) (v : V) :
    v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ B, v = a • e} ↔
      ∃ e ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}, v = c • e :=
  _root_.UpperTheory.Reformulated.B.Ydb6.main R A B c h v

end Closure

theorem pull_preserve : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E E' K' _ _ ι' _ z EB E'B hE hE'
  have hx : ∀ s, mseg (joinCoord x z) s ≠ 0 → mseg x (restrictChart s) ≠ 0 := by
    intro s hs h
    apply hs
    have e : mseg (joinCoord x z) s =
        mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) := by
      simp only [mseg, Fintype.prod_sum_type]
      rfl
    rw [e, h, zero_mul]
  refine ⟨fun h s hs => ?_, fun h s hs => ⟨fun v hv => ?_, fun v hv => ?_⟩,
    fun c h s hs v => ?_⟩
  · rw [hE s hs, hE' s hs]
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, e, h _ (hx s hs) he, rfl⟩
  · rw [hE s hs] at hv
    rw [hE' s hs]
    exact exists_const_smul_mem _ _ _ (h _ (hx s hs)).1 hv
  · rw [hE' s hs] at hv
    rw [hE s hs]
    exact exists_const_smul_mem _ _ _ (h _ (hx s hs)).2 hv
  · rw [hE s hs, hE' s hs]
    exact mem_span_scaled _ _ _ c (h _ (hx s hs)) v

end GlobalTheory.CompanionTheory.Ar.Num.PullPreserve
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleShortExact
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def comb (t : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => s (.inr k)

theorem mseg_join (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

theorem chartRing_le (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0) :
    chartRing O (mseg x) (restrictChart s) ≤ chartRing O (mseg (joinCoord x z)) s := by
  have hw : mseg z (fun k => s (.inr k)) ≠ 0 := by
    rw [mseg_join] at hs
    exact right_ne_zero_of_mul hs
  unfold chartRing
  apply Algebra.adjoin_le
  rintro _ ⟨t, rfl⟩
  have h : mseg x t / mseg x (restrictChart s) =
      mseg (joinCoord x z) (comb t s) / mseg (joinCoord x z) s := by
    rw [mseg_join x z (comb t s), mseg_join x z s]
    exact (mul_div_mul_right _ _ hw).symm
  have h2 := div_mem_chartRing (o := O) (mseg (joinCoord x z)) s (comb t s)
  rw [← h] at h2
  exact h2

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N N₁ N₂ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (E : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V) (p : V →ₗ[Ω] V₂) (E₁ : ChartBundle O (mseg x) N₁ V₁) (E₂ : ChartBundle O (mseg x) N₂ V₂), IsSubQuot O x E i p E₁ E₂ → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB : ChartBundle O (mseg (joinCoord x z)) N V) (EB₁ : ChartBundle O (mseg (joinCoord x z)) N₁ V₁) (EB₂ : ChartBundle O (mseg (joinCoord x z)) N₂ V₂), IsPull O x z E EB → IsPull O x z E₁ EB₁ → IsPull O x z E₂ EB₂ → IsSubQuot O (joinCoord x z) EB i p EB₁ EB₂ := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N N₁ N₂ V _ _ V₁ _ _ V₂ _ _ E i p E₁ E₂ h K' _ _ ι' _ z EB EB₁ EB₂ hE hE₁ hE₂
  obtain ⟨hi, hp, hex, hc⟩ := h
  refine ⟨hi, hp, hex, fun s hs => ?_⟩
  have hx : mseg x (restrictChart s) ≠ 0 := by
    rw [mseg_join] at hs
    exact left_ne_zero_of_mul hs
  obtain ⟨h₁, h₂⟩ := hc _ hx
  have hF : LocFree (chartRing O (mseg x) (restrictChart s)) N₂
      ((E.lat (restrictChart s)).map p.toAddMonoidHom) := by
    rw [← h₂]
    exact ⟨fun a ha v hv => E₂.stable _ a ha v hv, E₂.frame _ hx⟩
  obtain ⟨c₁, c₂⟩ := SpanExact.span_comap_exact _ _ (chartRing_le x z s hs) i p hi hex
    (E.lat (restrictChart s)) N₂ (fun a ha v hv => E.stable _ a ha v hv) hF
  have e : EB.lat s = spanOver (chartRing O (mseg (joinCoord x z)) s)
      (E.lat (restrictChart s) : Set V) := hE s hs
  have e₁ : EB₁.lat s = spanOver (chartRing O (mseg (joinCoord x z)) s)
      (E₁.lat (restrictChart s) : Set V₁) := hE₁ s hs
  have e₂ : EB₂.lat s = spanOver (chartRing O (mseg (joinCoord x z)) s)
      (E₂.lat (restrictChart s) : Set V₂) := hE₂ s hs
  rw [e, e₁, e₂, h₁, h₂]
  exact ⟨c₁.symm, c₂.symm⟩

end GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsCurveOfFunctionField
section
noncomputable section

open GroundTheory.FunctionField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isFunctionField_of_fg_trdeg {k κ : Type} [Field k] [Field κ] [Algebra k κ]
    (hfg : (⊤ : IntermediateField k κ).FG) (htr : Algebra.trdeg k κ = 1) :
    IsFunctionField k κ := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k κ
  have hcard : Cardinal.mk s = 1 := by rw [hs.cardinalMk_eq_trdeg, htr]
  obtain ⟨⟨x, hx⟩⟩ : Nonempty s := by
    rw [← Cardinal.mk_ne_zero_iff, hcard]
    exact one_ne_zero
  have hsx : s = {x} := by
    have hsub : Subsingleton s := by
      rw [← Cardinal.le_one_iff_subsingleton, hcard]
    ext y
    constructor
    · intro hy
      have := Subsingleton.elim (⟨y, hy⟩ : s) ⟨x, hx⟩
      simpa using congrArg Subtype.val this
    · rintro rfl
      exact hx
  have htrx : Transcendental k x := hs.1.transcendental ⟨x, hx⟩
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) κ := by
    have := hs.isAlgebraic_field
    rwa [Subtype.range_coe, hsx] at this
  obtain ⟨t, ht⟩ := hfg
  have hfd : ∀ F : IntermediateField k κ, Algebra.IsAlgebraic F κ → FiniteDimensional F κ := by
    intro F hF
    have hle : IntermediateField.adjoin k (↑t : Set κ) ≤
        (IntermediateField.adjoin F (↑t : Set κ)).restrictScalars k :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin F _)
    have htop : IntermediateField.adjoin F (↑t : Set κ) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y ∈ IntermediateField.adjoin k (↑t : Set κ) := by
        rw [ht]
        exact IntermediateField.mem_top
      exact hle hy
    have h1 : FiniteDimensional F (IntermediateField.adjoin F (↑t : Set κ)) :=
      IntermediateField.finiteDimensional_adjoin fun y _ => (hF.isAlgebraic y).isIntegral
    rw [htop] at h1
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  exact ⟨⟨x, htrx, hfd _ halg⟩⟩

section

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsFunctionField k κ]

def placesCurve : GlobalTheory.CompanionTheory.Ar.Crv.ACurve κ where
  I := Place k κ
  v := fun i => i.valuation
  w := fun i => i.deg
  fin := fun x hx => by
    refine (Place.finite_ord_ne_zero (k := k) x).subset fun i hi h0 => hi ?_
    have h := i.valuation_eq_exp_neg_ord hx
    rw [h, h0]
    simp
  prod := fun x hx => by
    classical
    have h := Divisor.deg_divisor (k := k) x
    rw [Divisor.deg_eq_sum] at h
    rw [finsum_eq_sum_of_support_subset (s := (divisor x : Divisor k κ).support)]
    · have : ∑ i ∈ (divisor x : Divisor k κ).support,
          ((i.deg : ℤ) * WithZero.log (i.valuation x)) =
          - ∑ i ∈ (divisor x : Divisor k κ).support, (divisor x : Divisor k κ) i * (i.deg : ℤ) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [divisor_apply, Place.ord]
        ring
      rw [this, h, neg_zero]
    · intro i hi
      simp only [Function.mem_support] at hi
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, divisor_apply, Place.ord]
      intro h0
      apply hi
      have : WithZero.log (i.valuation x) = 0 := by omega
      rw [this, mul_zero]

end

theorem exists_curve_of_function_field :
    ∀ (k κ : Type) [Field k] [Field κ] [Algebra k κ], (⊤ : IntermediateField k κ).FG →
      Algebra.trdeg k κ = 1 → ∃ C : GlobalTheory.CompanionTheory.Ar.Crv.ACurve κ, (∀ i, 0 < C.w i) ∧
        (∀ i (a : k), a ≠ 0 → C.v i (algebraMap k κ a) = 1) ∧
        (∀ i, Function.Surjective (C.v i)) ∧
        ∀ W : ValuationSubring κ, W ≠ ⊤ → (∀ a : k, algebraMap k κ a ∈ W) →
          ∃! i, (C.v i).valuationSubring = W := by
  intro k κ _ _ _ hfg htr
  haveI : IsFunctionField k κ := isFunctionField_of_fg_trdeg hfg htr
  have key : ∀ i : Place k κ, (i.valuation).valuationSubring = i.ring := fun i => by
    ext y
    rw [Valuation.mem_valuationSubring_iff]
    exact Place.valuation_le_one_iff i y
  refine ⟨placesCurve k κ, fun i => ?_, fun i a ha => ?_, fun i => ?_, fun W hW hk => ?_⟩
  · exact Place.deg_pos i
  · exact Place.valuation_algebraMap' i ha
  · exact Place.valuation_surjective i
  · refine ⟨⟨W, hW, hk⟩, key _, fun j hj => ?_⟩
    exact Place.ext ((key j).symm.trans hj)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalLinearTermComposition
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem lin_comp_chain : ∀ (R : Type) [CommRing R] (d : ℕ) (φ ψ : Pt R 1 d), (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → lin (comp1 φ ψ) 1 = lin φ 1 * lin ψ 1 ∧ lin (pt R (n := 1) d 0) 1 = 1 ∧ ∀ p : ℕ, 1 ≤ p → lin (comp1 φ (ptPow R d p 0)) p = lin φ 1 ∧ lin (comp1 φ (comp1 ψ (ptPow R d p 0))) p = lin φ 1 * lin ψ 1 :=
  @PositivityTheory.HtPt.Ca.lin_comp

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeKernelImageLattice
section
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CompanionTheory.Ar.PtSeq

theorem pt_seq_lin : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (τ : Sg), w ≠ 0 → mulLat w (stdLat RC _) ≤ D.af RC p (χ τ) → D.af RC p (χ τ) ≤ stdLat RC _ → ∀ (ht : (Fin n → C) →ₗ[C] (Fin (s τ) → C)) (hb : (Fin (r τ) → C) →ₗ[C] (Fin n → C)), Function.Injective hb → LinearMap.range hb = LinearMap.ker ht → (stdLat RC _).map ht.toAddMonoidHom = D.omHT τ → (stdLat RC _).comap hb.toAddMonoidHom = D.W τ → (D.hh RC p (χ τ)).map ht.toAddMonoidHom = D.om τ → (D.hh RC p (χ τ)).comap hb.toAddMonoidHom = divLat w (D.lie τ) → (∀ b c, (b, c) ∈ D.Del τ ↔ w • b ∈ stdLat RC _ ∧ c - ht b ∈ D.omHT τ) → (∀ a b, (a, b) ∈ D.Gam τ ↔ w • a ∈ D.W τ ∧ b - hb a ∈ stdLat RC _) → D.imH RC p τ (χ τ) = D.om τ ∧ D.kerH RC p τ (χ τ) = divLat w (D.lie τ) :=
  @PositivityTheory.Xgn.t_pt_seq_lin

end GlobalTheory.CompanionTheory.Ar.PtSeq
end

