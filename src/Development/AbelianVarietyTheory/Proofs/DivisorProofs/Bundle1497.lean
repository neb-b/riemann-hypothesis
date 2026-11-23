module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingMapsLiftVerticalDeformationsAffine
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS


open TrivSqZeroExt in
theorem exists_spMap_fst_eq {S : Type} [CommRing S] (s : Sp (DualNumber S)) :
    ∃ t : Sp S, spMap (fstHom S S S).toRingHom t = s := by
  refine ⟨PrimeSpectrum.comap (inlHom S S) s, ?_⟩
  show PrimeSpectrum.comap _ (PrimeSpectrum.comap _ s) = s
  ext x
  have hr : inr x.snd ∈ s.asIdeal := s.2.mem_of_pow_mem 2 (by
    rw [show (inr x.snd : DualNumber S) ^ 2 = 0 by ext <;> simp [pow_two]]
    exact s.asIdeal.zero_mem)
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change inl x.fst ∈ s.asIdeal ↔ x ∈ s.asIdeal
  have e1 : inl x.fst + inr x.snd = x := inl_fst_add_inr_snd_eq x
  have e2 : inl x.fst = x - inr x.snd := eq_sub_of_add_eq e1
  constructor
  · intro h
    rw [← e1]
    exact s.asIdeal.add_mem h hr
  · intro h
    rw [e2]
    exact s.asIdeal.sub_mem h hr

theorem le_preimage_of_fst {S : Type} [CommRing S] {T : Scheme.{0}} (x : Sp (DualNumber S) ⟶ T) (V : T.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  obtain ⟨t, rfl⟩ := exists_spMap_fst_eq s
  exact h (Set.mem_univ t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

theorem exists_dualLift {S : Type} [CommRing S] [Algebra c.F S] {Q : FrPt Xo c S} {v : FrPt Xo c (DualNumber S)}
    (hv : FrMap (TrivSqZeroExt.fstHom c.F S S) v Q) {z : Sp S ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q)
    (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ zv : Sp (DualNumber S) ⟶ M.X, zv ≫ toFlag M = X.ptY v ∧
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ zv = z := by
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ X.ptY v = z ≫ toFlag M :=
    (X.ptY_frMap hv).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY v ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_fst _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY v) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY v := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_fst _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, hred⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

def vertMat {S : Type} [CommRing S] (b : VIx Dw) (σ : E →+* ℂ) :
    Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) (DualNumber S) :=
  Matrix.of fun i j => TrivSqZeroExt.inl ((1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) i j) +
    TrivSqZeroExt.inr ((Pi.single b.toF (1 : S) : GlobalTheory.FlagTan.FIx Dw → S) (some ⟨σ, i, j⟩))

theorem isUnit_det_vertMat {S : Type} [CommRing S] (b : VIx Dw) (σ : E →+* ℂ) :
    IsUnit (vertMat (S := S) b σ).det := by
  have e : (TrivSqZeroExt.fstHom S S S).toRingHom.mapMatrix (vertMat (S := S) b σ) = 1 := by
    ext i j; simp [vertMat]
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  show IsUnit ((TrivSqZeroExt.fstHom S S S).toRingHom _)
  rw [RingHom.map_det, e, Matrix.det_one]
  exact isUnit_one

theorem exists_vertLift (k : X.F.J) (W : M.X.Opens) (hW : IsAffineOpen W)
    (hle : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) :
    ∃ e : VIx Dw → (Γ(M.X, W) →+* DualNumber Γ(M.X, W)), (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W) →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b : VIx Dw, ∃ w : FrPt Xo c (DualNumber K),
          IsVert Q (Pi.single b.toF (1 : K)) w ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW ≫ toFlag M = X.ptY w := by
  have hτo : ⊤ ≤ tau hW ⁻¹ᵁ M.off := tau_le hW (hle.trans inf_le_left)
  have hτk : ⊤ ≤ (tau hW ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun x hx => tau_le hW (hle.trans inf_le_right) hx
  have hF : ⊤ ≤ (tau hW ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun x hx => by
    have := hτo hx
    rw [M.off_eq] at this
    exact this
  obtain ⟨_, hch⟩ := exists_chartFr _ hF
  obtain ⟨Q₀, hQ₀⟩ := hch k hτk
  have e₀ : tau hW ≫ toFlag M = X.ptY Q₀ := GlobalTheory.FlagMod.FlagCover.eq_ptY hQ₀.lies
  obtain ⟨Q₁, hQ₁⟩ := GlobalTheory.FlagTan.exists_frMap (TrivSqZeroExt.inlAlgHom c.F Γ(M.X, W) Γ(M.X, W)) Q₀
  have hred : FrMap (TrivSqZeroExt.fstHom c.F Γ(M.X, W) Γ(M.X, W)) Q₁ Q₀ :=
    GlobalTheory.FlagTan.frMap_of_comp hQ₁ (GlobalTheory.FlagTan.frMap_id Q₀) fun _ => rfl
  have hV : ∀ b : VIx Dw, ∃ V : FrPt Xo c (DualNumber Γ(M.X, W)),
      GlobalTheory.Frames.FrChg (vertMat b) ((1 : (DualNumber Γ(M.X, W))ˣ) : DualNumber Γ(M.X, W)) Q₁ V := fun b =>
    (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ Q₁ (vertMat b) 1 (isUnit_det_vertMat b)).exists
  choose V hV using hV
  have hVr : ∀ b, FrMap (TrivSqZeroExt.fstHom c.F Γ(M.X, W) Γ(M.X, W)) (V b) Q₀ := fun b => by
    refine (GlobalTheory.FlagTan.frMap_iff_frChg (hV b) hred).2 ?_
    convert (GlobalTheory.Frames.frChg_calculus E H Dw l Xo c Γ(M.X, W)).2.1 Q₀ using 2 with σ
    · ext i j; simp [vertMat]
    · simp
  choose zv hzv hzr using fun b => exists_dualLift M (hVr b) e₀ hτo
  have hzW : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ W := fun b => le_preimage_of_fst _ _ (by rw [hzr b]; exact tau_le hW le_rfl)
  refine ⟨fun b => GlobalTheory.FlagMod.ev (zv b) W (hzW b), fun b s => ?_, ?_⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom Γ(M.X, W) Γ(M.X, W) Γ(M.X, W)).toRingHom ≫ zv b) ⁻¹ᵁ W := by
      rw [hzr b]; exact tau_le hW le_rfl
    have h1 := GlobalTheory.FlagMod.ev_spMap _ (zv b) W (hzW b) h'
    rw [GlobalTheory.FlagMod.ev_congr (hzr b) W h' (tau_le hW le_rfl), GlobalTheory.FlagMod.ev_tau_self] at h1
    exact (DFunLike.congr_fun h1 s).symm
  intro K _ _ ψ hk Q hQ b

  have hx : frX Q = spMap ψ ≫ frX Q₀ := by
    let w₀ : Sp Γ(M.X, W) ⟶ X.Yo := pullback.lift (tau hW ≫ toFlag M) (frX Q₀) hQ₀.over.symm
    let w₁ : Sp K ⟶ X.Yo := pullback.lift ((spMap ψ ≫ tau hW) ≫ toFlag M) (frX Q) hQ.over.symm
    have e : w₁ = spMap ψ ≫ w₀ := by
      rw [← cancel_mono X.inc]
      simp only [w₀, w₁, Category.assoc, pullback.lift_fst]
    have := congrArg (· ≫ pullback.snd X.π Y.j) e
    simpa only [w₀, w₁, Category.assoc, pullback.lift_snd] using this
  have hs : spMap (algebraMap c.F K) = spMap (ψ.comp (algebraMap c.F Γ(M.X, W))) := by
    rw [← frX_snd Q, hx, Category.assoc, frX_snd Q₀, spMap_comp']
  have hψ : ψ.comp (algebraMap c.F Γ(M.X, W)) = algebraMap c.F K :=
    (congrArg CommRingCat.Hom.hom (Spec.map_injective hs)).symm
  let φ : Γ(M.X, W) →ₐ[c.F] K := { ψ with commutes' := fun r => DFunLike.congr_fun hψ r }
  let φε : DualNumber Γ(M.X, W) →ₐ[c.F] DualNumber K :=
    { dualMap ψ with
      commutes' := fun r => by
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl', ← DFunLike.congr_fun hψ r] }
  obtain ⟨Q', hQ'⟩ := GlobalTheory.FlagTan.exists_frMap φ Q₀
  have eQ : Q = Q' := hQ.unique (hQ₀.frMap hQ' (by rw [Category.assoc]) hk)
  subst eQ
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.FlagTan.exists_frMap φε Q₁
  obtain ⟨w, hw⟩ := GlobalTheory.FlagTan.exists_frMap φε (V b)
  refine ⟨w, ⟨y₀, GlobalTheory.FlagTan.frMap_of_comp hQ' (GlobalTheory.FlagTan.frMap_comp (χ := φε.comp (TrivSqZeroExt.inlAlgHom c.F Γ(M.X, W) Γ(M.X, W))) hQ₁ hy₀ fun _ => rfl) fun a => ?_, ?_⟩, ?_⟩
  · ext <;> simp [φ, φε, dualMap]
  · have h2 := (GlobalTheory.FlagTan.frMap_iff_frChg (hV b) hy₀).1 hw
    unfold GlobalTheory.FlagTan.IsShift
    convert h2 using 2 with σ
    · ext i j <;> simp [GlobalTheory.FlagTan.unip, vertMat, φε, dualMap, Matrix.one_apply, Pi.single_apply] <;> split_ifs <;> simp
    · ext <;> simp [GlobalTheory.FlagTan.unip₀, φε, dualMap, GlobalTheory.FlagTan.VIx.toF]
  · have h3 : spMap (GlobalTheory.FlagMod.ev (zv b) W (hzW b)) ≫ tau hW = zv b := GlobalTheory.FlagMod.spMap_ev (zv b) hW (hzW b)
    rw [← spMap_comp', Category.assoc, ← Category.assoc (spMap _) (tau hW), h3, hzv b]
    have e4 : dualMap ψ = φε.toRingHom := RingHom.ext fun _ => rfl
    rw [e4]
    exact X.ptY_frMap hw

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueModificationLiftSqZeroFlag
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModifLift

theorem spMap_fst_surjective_sqZero (K : Type) [Field K] (ι : Type) :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) := by
  intro p
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change x.fst ∈ (⊥ : Ideal K) ↔ x ∈ PrimeSpectrum.asIdeal p
  rw [Ideal.mem_bot]
  constructor
  · intro hx
    apply p.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two, show x = TrivSqZeroExt.inr x.snd from TrivSqZeroExt.ext hx rfl,
        TrivSqZeroExt.inr_mul_inr]
    rw [this]
    exact Ideal.zero_mem _
  · intro hx
    by_contra h0
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)

theorem exists_lift_sqZero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
    (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] {ι : Type} (z : Sp K ⟶ M.X)
    (hz : ⊤ ≤ z ⁻¹ᵁ M.off) (w : Sp (TrivSqZeroExt K (ι → K)) ⟶ X.YY)
    (hw : spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w = z ≫ toFlag M) :
    ∃ w' : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, w' ≫ toFlag M = w ∧
      spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w' = z ∧
      ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ w' ⁻¹ᵁ O := by
  set f := spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom with hf
  have hs := spMap_fst_surjective_sqZero K ι
  have hr : Set.range w ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := hs t
    refine ⟨M.σ (z s), ?_⟩
    change (z ≫ M.σ ≫ inc₀ X Z) s = (f ≫ w) s
    rw [hw]
  set w₀ := IsOpenImmersion.lift (inc₀ X Z) w hr with hw₀
  have hw₀f : w₀ ≫ inc₀ X Z = w := IsOpenImmersion.lift_fac _ _ _
  have hfw₀ : f ≫ w₀ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw₀f, hw, Category.assoc]
  have hzU : ∀ s, M.σ (z s) ∈ U₀ X Z := fun s => by
    have := hz (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hU : ⊤ ≤ w₀ ⁻¹ᵁ U₀ X Z := by
    intro t _
    obtain ⟨s, rfl⟩ := hs t
    change (f ≫ w₀) s ∈ U₀ X Z
    rw [hfw₀]
    exact hzU s
  obtain ⟨w', hw', -⟩ := M.existsUnique_lift w₀ hU
  have hU' : ⊤ ≤ (f ≫ w₀) ⁻¹ᵁ U₀ X Z := fun s _ => hU (Set.mem_univ (f s))
  have hfw' : f ≫ w' = z := by
    obtain ⟨_, -, huniq⟩ := M.existsUnique_lift (f ≫ w₀) hU'
    exact (huniq _ (show (f ≫ w') ≫ M.σ = f ≫ w₀ by rw [Category.assoc, hw'])).trans (huniq z hfw₀.symm).symm
  refine ⟨w', ?_, hfw', fun O hO t _ => ?_⟩
  · rw [toFlag, ← Category.assoc, hw', hw₀f]
  · obtain ⟨s, rfl⟩ := hs t
    change (f ≫ w') s ∈ O
    rw [hfw']
    exact hO (Set.mem_univ s)

end GlobalTheory.ModifLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformation
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open scoped Classical

namespace GlobalTheory.FlagTan

open GlobalTheory.Frames GlobalTheory.AllWt
open TrivSqZeroExt hiding map lift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]


variable (Dw K) in
def horExt (Φ : Finset (E →+* ℂ)) : (HIx Dw Φ → K) →ₗ[K] (TIx Dw Φ → K) :=
  LinearMap.pi fun b => Sum.elim (fun k => LinearMap.proj k) (fun _ => 0) b


variable (c) in
def horMap (Φ : Finset (E →+* ℂ)) : TrivSqZeroExt K (HIx Dw Φ → K) →ₐ[c.F] TrivSqZeroExt K (TIx Dw Φ → K) :=
  (TrivSqZeroExt.map (horExt Dw K Φ)).restrictScalars c.F

theorem fst_horMap {Φ : Finset (E →+* ℂ)} (a : TrivSqZeroExt K (HIx Dw Φ → K)) : (horMap c Φ a).fst = a.fst :=
  fst_map _ a

theorem dir_horMap {Φ : Finset (E →+* ℂ)} (m : TIx Dw Φ → K) (a : TrivSqZeroExt K (HIx Dw Φ → K)) :
    dir c m (horMap c Φ a) = dir c (m ∘ Sum.inl) a := by
  ext
  · simp [fst_horMap]
  · simp [snd_dir, horMap, horExt, Fintype.sum_sum_type]

def vertDirs (Φ : Finset (E →+* ℂ)) : FIx Dw → TIx Dw Φ → K :=
  fun k b => Sum.elim (fun _ => 0) (fun w : VIx Dw => if k = w.toF then 1 else 0) b

end GlobalTheory.FlagTan


set_option maxHeartbeats 1000000 in
open GlobalTheory.FlagTan GlobalTheory.Frames GlobalTheory.AllWt in
open TrivSqZeroExt hiding map lift in
theorem GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (psiSet H) P → ∃ (W : FrPt Xo c (TrivSqZeroExt K (TIx Dw (psiSet H) → K))) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)), FrMap (TrivSqZeroExt.fstHom c.F K (TIx Dw (psiSet H) → K)) W P ∧ (∀ b, FrMap (GlobalTheory.FlagTan.dir c (Pi.single b (1 : K))) W (v b)) ∧ IsTanFrame (psiSet H) P v ∧ ∀ (m : TIx Dw (psiSet H) → K) (u P₀ : FrPt Xo c (DualNumber K)), FrMap (GlobalTheory.FlagTan.dir c m) W u → FrMap (GlobalTheory.FlagTan.cst c K) P P₀ → X.ptY u = X.ptY P₀ → m = 0 := by
  intro E _ _ _ H Dw l Xo c Y X K _ _ P hK
  obtain ⟨XH, h1, h2, hU⟩ := hK
  obtain ⟨WH, rfl, hWH⟩ := exists_lift P XH h1 h2
  obtain ⟨W₀, hW₀⟩ := exists_frMap (horMap c (K := K) (Dw := Dw) (psiSet H)) WH
  let n : FIx Dw → TIx Dw (psiSet H) → K := vertDirs (psiSet H)
  obtain ⟨W, hW, -⟩ := existsUnique_frChg E H Dw l Xo c _ W₀ _ (isUnit_unip₀ (K := K) n).unit (isUnit_det_unip n)
  have key : ∀ (m : TIx Dw (psiSet H) → K) (z₀ z : FrPt Xo c (DualNumber K)), FrMap (dir c m) W₀ z₀ →
      IsShift (fun k => ∑ b, n k b * m b) z₀ z → FrMap (dir c m) W z := fun m z₀ z k₀ k => by
    refine (frMap_iff_frChg hW k₀).2 ?_
    unfold IsShift at k
    convert k using 2 with τ
    · ext i j <;> simp [unip]
    · ext <;> simp [unip₀]
  have shift : ∀ (m : TIx Dw (psiSet H) → K) (u : FrPt Xo c (DualNumber K)), FrMap (dir c m) W u →
      ∃ z₀, FrMap (dir c m) W₀ z₀ ∧ IsShift (fun k => ∑ b, n k b * m b) z₀ u := fun m u hu => by
    obtain ⟨z₀, hz₀⟩ := exists_frMap (dir c m) W₀
    obtain ⟨z, hz, -⟩ := existsUnique_isShift (fun k => ∑ b, n k b * m b) z₀
    exact ⟨z₀, hz₀, frMap_unique (key m z₀ z hz₀ hz) hu ▸ hz⟩
  have hbase : ∀ (m : TIx Dw (psiSet H) → K) (z₀ : FrPt Xo c (DualNumber K)), FrMap (dir c m) W₀ z₀ →
      FrMap (dir c (m ∘ Sum.inl)) WH z₀ := fun m z₀ h => frMap_comp hW₀ h fun a => dir_horMap m a
  have hfst : FrMap (fstHom c.F K (TIx Dw (psiSet H) → K)) W P := by
    have h0 : FrMap (fstHom c.F K (TIx Dw (psiSet H) → K)) W₀ P :=
      frMap_of_comp hW₀ hWH fun a => fst_horMap (c := c) a
    refine (frMap_iff_frChg hW h0).2 ?_
    convert (frChg_calculus E H Dw l Xo c _).2.1 P using 2 with τ
    · ext i j; by_cases h : i = j <;> simp [unip, Matrix.one_apply, h]
    · simp [unip₀]
  have hdef : ∀ (m : TIx Dw (psiSet H) → K) (u : FrPt Xo c (DualNumber K)), FrMap (dir c m) W u → IsDef P u :=
    fun m u h => frMap_of_comp h hfst fun a => fst_dir (c := c) m a
  choose v hv using fun b : TIx Dw (psiSet H) => exists_frMap (dir c (Pi.single b (1 : K))) W
  refine ⟨W, v, hfst, hv, ⟨fun k => ?_, fun w => ?_⟩, fun m u P₀ hu hP₀ hpt => ?_⟩
  · obtain ⟨z₀, hz₀, hs⟩ := shift _ _ (hv (.inl k))
    have e0 : (fun k' => ∑ b, n k' b * (Pi.single (Sum.inl k) (1 : K) : TIx Dw (psiSet H) → K) b) = 0 := by
      funext k'; simp [n, vertDirs, Fintype.sum_sum_type, Pi.single_apply]
    rw [e0] at hs
    have ev : v (.inl k) = z₀ := (existsUnique_isShift 0 z₀).unique hs (isShift_zero z₀)
    have e1 : (Pi.single (Sum.inl k) (1 : K) : TIx Dw (psiSet H) → K) ∘ Sum.inl = Pi.single k 1 := by
      funext h; simp [Pi.single_apply]
    have hb := hbase _ _ hz₀
    rw [e1] at hb
    have hd := hdef _ _ (hv (.inl k))
    refine ⟨hd, ((hU _ hd.isTanX).2 _).2 ?_⟩
    rw [ev]; exact hb.1
  · obtain ⟨z₀, hz₀, hs⟩ := shift _ _ (hv (.inr w))
    have e0 : (fun k' => ∑ b, n k' b * (Pi.single (Sum.inr w) (1 : K) : TIx Dw (psiSet H) → K) b) =
        Pi.single w.toF 1 := by
      funext k'; simp [n, vertDirs, Fintype.sum_sum_type, Pi.single_apply]
    rw [e0] at hs
    have hc : FrMap (GlobalTheory.FlagTan.cst c K) P z₀ := by
      have hb := hbase _ _ hz₀
      refine frMap_of_comp (ψ := GlobalTheory.FlagTan.cst c K) hWH hb fun a => ?_
      ext <;> simp [snd_dir, Pi.single_apply]
    exact ⟨z₀, hc, hs⟩
  · obtain ⟨z₀, hz₀, hs⟩ := shift m u hu
    have hH := hbase m z₀ hz₀
    obtain ⟨t, hB⟩ : ∃ t, FrBor t P₀ u := by
      obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY P₀)
      obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd P₀) (X.lies_ptY P₀).1 k hz
      obtain ⟨t, ht⟩ := hQ.exists_frBor (X.lies_ptY P₀)
      obtain ⟨t', ht'⟩ := hQ.exists_frBor (hpt ▸ X.lies_ptY u)
      obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (DualNumber K)
      exact ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩
    have hd := hdef m u hu
    have e0 : m ∘ Sum.inl = 0 := by
      refine (hU u.x hd.isTanX).1.unique (hs.1.trans hH.1) ?_
      have ed : dir c (0 : HIx Dw (psiSet H) → K) = (cst c K).comp (fstHom c.F K (HIx Dw (psiSet H) → K)) :=
        AlgHom.ext fun a => by ext <;> simp [snd_dir]
      rw [hB.1, hP₀.1, ed, GlobalTheory.FlagMod.spMap_algComp, h2]
    have e0' : ∀ h, m (Sum.inl h) = 0 := fun h => congrFun e0 h
    have hz : z₀ = P₀ := by
      refine frMap_unique (frMap_of_comp hWH hH fun a => ?_) hP₀
      ext <;> simp [snd_dir, e0']
    rw [hz] at hs
    obtain ⟨g, hup, -, hc⟩ := (frBor_iff_frChg _ _ _).1 hB
    obtain ⟨hg, -⟩ := (frChg_exists_unique E H Dw l Xo c _ P₀ u).2 _ _ _ _ hc hs
    have hsum : ∀ w₀ : VIx Dw, ∑ b, n w₀.toF b * m b = m (Sum.inr w₀) := fun w₀ => by
      simp [n, vertDirs, Fintype.sum_sum_type, VIx.toF_injective.eq_iff]
    have ev : ∀ w₀ : VIx Dw, m (Sum.inr w₀) = 0 := by
      rintro ⟨σ, ⟨i, j⟩, hij⟩
      have := congrArg (fun g => (g σ i j).snd) hg
      rw [← hsum]
      simp only [VIx.toF]
      simpa [hup σ i j hij, unip] using this.symm
    funext b
    rcases b with b | b
    · exact e0' b
    · exact ev b
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExplicitArithmeticHilbertSamuelBound
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShortTop

theorem geoBound_of_abstract : Quoted → BertiniNF → HeightTie → SlopeBound → GeoBound := by
  intro hQ hB hT hS F _ _ X Λ₀ hG h hh
  obtain ⟨dd, f, hdpos, hf, hfh⟩ := hh
  obtain ⟨hdel, Q, hQ0, hQs⟩ := hB F X.toTuple X.geom hG.bir dd f hf
  have hHyp := _root_.GlobalTheory.HSShort.GeoHyp.sysOf_hyp F X Λ₀ hG
  have hFlat := _root_.GlobalTheory.HSShort.flatAt_of_simpleAt hQ F X Λ₀ hG dd f Q hQs
  have hirr : Irreducible f := GlobalTheory.ChowHt.irreducible_of_irreducible_map hf.irred
  obtain ⟨hpos, hcl⟩ := hS F (Tot X.toGeo) (sysOf X Λ₀) hHyp dd f Q (by omega) hf.homog hirr hQ0 hFlat
  have hfr : Module.finrank F ((sysOf X Λ₀).V (sysOf X Λ₀).T) = X.d := by
    rw [X.d_eq_finrank]; exact (inclEquiv X X.T).finrank_eq.symm
  have hdeg : deg ((sysOf X Λ₀).nm (sysOf X Λ₀).T) ((sysOf X Λ₀).M (sysOf X Λ₀).T) = X.degM X.T := by
    have := GlobalTheory.IsoDeg.deg_map_eq F (X.V X.T) (LinearMap.range (incl X X.T)) (X.nm X.T)
      (comap (X.nm X.T) (inclEquiv X X.T).symm.toLinearMap (inclEquiv X X.T).symm.injective) (inclEquiv X X.T)
      (fun σ m c g => by simp only [csq, HermTools.comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]) (X.M X.T) (X.full X.T).fg
    exact this
  have hTie := (hT F X.toHermSys X.abelian₂ hHyp.lat h ⟨dd, f, hdpos, hf, hfh⟩ dd 1 f 1 hf le_rfl one_ne_zero).2
  rw [hfr, hdeg] at hcl
  have hd' : ((X.del : ℤ) : ℝ) = (dd : ℝ) := by rw [← hdel]; push_cast; rfl
  rw [hd']
  refine _root_.GlobalTheory.HSShortNum.claimS_to_hsClaimS X.T X.D X.n X.abelian₂ X.beta Λ₀ X.LamD X.LamT dd h _ X.d (X.degM X.T)
    (by exact_mod_cast hHyp.one_le) hHyp.le_T (by exact_mod_cast X.one_le_n) hHyp.lat.one_le hHyp.one_le_beta
    (by exact_mod_cast hdpos) ?_ hcl
  have h2 : h - (Real.log X.n + 1) / 2 ≤ ht X.w X.A f / (((X.D : ℝ) + 1) * dd) := by
    simp at hTie; linarith
  exact h2

end GlobalTheory.HSShortTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichStarRep
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

noncomputable section

namespace GlobalTheory.DetInv

open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta (epsTate epsEquiv epsPairing toO pairingO bQuot Realizes)

section Group

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)

theorem pairing_dual_bidual (t : G.Tate) (u : G.dual.Tate) :
    pairing G.dual O u (tateMap G G.dual.dual O G.bidual.hom t) = pairing G O t u :=
  muRoot_ext fun n => by
    rw [muRoot_pairing, muRoot_pairing]
    have h1 : charElem (G := G.dual) (tateMap G G.dual.dual O G.bidual.hom t) n =
        WithConv.toConv (t.pt n).toLinearMap :=
      (charHom_app_muT _ n).symm.trans (dualChar_app_muT t n)
    rw [h1]
    exact (apply_charElem u n _).symm

end Group

end GlobalTheory.DetInv
end
end

