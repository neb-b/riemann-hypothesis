module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.CongAtIdem

theorem read_rel {A B K E : Type} [CommRing A] [CommRing B] [CommRing K] [CommRing E] {m n : Type} [Fintype m] [Fintype n]
    (t : A →+* B) (φ : B →+* K) (i : E →+* A) (j : E →+* B) (hij : ∀ x, t (i x) = j x) {e : A} (he : φ (t e) = 1)
    (X : Matrix m m A) (Z : Matrix n n A) (γ γ₀ : Matrix m n E) (v : Matrix m n A) (k : ℕ)
    (h : γ₀.map (fun r => e * i r) = X * γ.map (fun r => e * i r) * Z + k • v) (r : m) (s : n) :
    φ ((X.map t * γ.map j * Z.map t - γ₀.map j) r s) = -((k : K) * φ (t (v r s))) := by
  have h1 := congrArg (fun W : Matrix m n A => φ (t (W r s))) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, map_add (f := _), map_sum, map_mul, he,
    one_mul, hij, nsmul_eq_mul, map_natCast] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, h1]
  ring

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem adAt_toEAf_of_isIdemAt {f : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hf : Formalism.L2.NTheta.IsIdemAt f P) : adAt D.host.F P (toEAf D f) = 1 := by
  let ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (afIso D.host.F D.host.E)
  have h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := fun x =>
    afIso_tmul_one D.host.F D.host.E x
  have h2 : ∀ y, y ∈ intAE D ↔ ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y Q) ≤ 1 := fun y =>
    (GlobalTheory.IdemSupport.mem_intAE_iff y).trans (mem_rInt_iff D.host.F D.host.E _)
  exact GlobalTheory.ChrOff.comp_idem ι h1 h2 hf

theorem adAt_toEAf_of_isIdemSum {e : AE D} {Ps : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    (he : IsIdemSum e Ps) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ Ps) :
    adAt D.host.F P (toEAf D e) = 1 := by
  obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt he hP
  have h := congrArg (fun z => adAt D.host.F P (toEAf D z)) hae
  simp only [map_mul, adAt_toEAf_of_isIdemAt ha, one_mul] at h
  exact h

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem isIntegral_of_eq {x : D.host.E} (h : ∃ r : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E r = x) :
    IsIntegral ℤ x := by
  obtain ⟨r, rfl⟩ := h
  exact r.2

theorem tmul_one_mem_rInt {x : D.host.E} (hx : IsIntegral ℤ x) :
    x ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨x, ⟨⟨x, hx⟩, rfl⟩⟩, rfl⟩)

theorem one_tmul_mem_rInt {α : FiniteAdeleRing (𝓞 D.host.F) D.host.F} (hα : α ∈ intAf D.host.F) :
    (1 : D.host.E) ⊗ₜ[D.host.F] α ∈ Formalism.L2.DIV.RInt D.host.F D.host.E :=
  Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩)

theorem exists_den_stdHom (S T : HSp D) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ stdHom S T, ∀ r s,
    ((d : EF D) * toEAf D (v r s) : Formalism.L2.DIV.AfE D.host.F D.host.E) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E := by
  obtain ⟨a0, ha0, hfrac⟩ := D.host.AA.isFractional
  have ha0' : ((a0 : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero ⟨a0, ha0⟩ (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨d, hd, hint⟩ := GlobalTheory.AdeleBaseChange.exists_nat_mul_integral
    (insert ((a0 : D.host.E))⁻¹ (Finset.image (fun p : Fin S.rank × Fin S.rank => S.gram p.1 p.2) Finset.univ))
  have hx0 : IsIntegral ℤ ((d : D.host.E) * ((a0 : D.host.E))⁻¹) := by
    rw [← nsmul_eq_mul]; exact isIntegral_of_eq (hint _ (Finset.mem_insert_self _ _))
  have hG : ∀ k j, IsIntegral ℤ ((d : D.host.E) * S.gram k j) := fun k j => by
    rw [← nsmul_eq_mul]
    exact isIntegral_of_eq (hint _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)))
  refine ⟨d * d, Nat.mul_pos hd hd, fun v hv => ?_⟩
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r c
    have hint' : IsIntegral ℤ (((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) := by
      have hA : IsIntegral ℤ ((a0 : D.host.E) * a) := by
        obtain ⟨y, hy⟩ := hfrac a ha
        refine isIntegral_of_eq ⟨y, ?_⟩
        rw [hy, Algebra.smul_def]
      have hsum : IsIntegral ℤ (∑ k, star (s k) * ((d : D.host.E) * S.gram k c)) :=
        IsIntegral.sum _ fun k _ => IsIntegral.mul
          ((hs k).map (starRingEnd D.host.E).toIntAlgHom) (hG k c)
      have e : ((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c) =
          ((d : D.host.E) * ((a0 : D.host.E))⁻¹) * ((a0 : D.host.E) * a) * t r *
            ∑ k, star (s k) * ((d : D.host.E) * S.gram k c) := by
        have hx : ((a0 : D.host.E))⁻¹ * (a0 : D.host.E) = 1 := inv_mul_cancel₀ ha0'
        have e2 : ∑ k, star (s k) * ((d : D.host.E) * S.gram k c) = (d : D.host.E) * ∑ k, star (s k) * S.gram k c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [e2]; push_cast
        linear_combination (-((d : D.host.E) * d * a * t r * ∑ k, star (s k) * S.gram k c)) * hx
      rw [e]
      exact ((hx0.mul hA).mul (ht r)).mul hsum
    change ((d * d : ℕ) : EF D) * ((a * t r * ∑ k, star (s k) * S.gram k c) ⊗ₜ[D.host.F] α) ∈ _
    have e3 : ((d * d : ℕ) : EF D) * ((a * t r * ∑ k, star (s k) * S.gram k c) ⊗ₜ[D.host.F] α) =
        ((((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) ⊗ₜ[D.host.F]
          (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] α) := by
      have hc : ((d * d : ℕ) : EF D) = ((d * d : ℕ) : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
        (map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
          (B := FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d * d)).symm
      rw [hc]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e3]
    exact mul_mem (tmul_one_mem_rInt hint') (one_tmul_mem_rInt hα)
  | zero => intro r s; simp
  | add x y _ _ hx hy => intro r s; rw [Matrix.add_apply, RingHom.map_add (toEAf D), mul_add]; exact add_mem (hx r s) (hy r s)
  | neg x _ hx => intro r s; rw [Matrix.neg_apply, RingHom.map_neg (toEAf D), mul_neg]; exact neg_mem (hx r s)

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem finM_rfl (V : HSp D) (x : GA D V) : finM V rfl x = (Formalism.L2.Theta.mt V x).map (toEAf D) := by
  simp [finM, finCongr_refl]

theorem mt_mul' (V : HSp D) (x y : GA D V) :
    Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := by
  show (matHom V (x * y)).1 = (matHom V x).1 * (matHom V y).1
  rw [map_mul, Units.val_mul]

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem inv_val_eq (V : HSp D) (x : GA D V) (Y : GL (Fin V.rank) (EF D)) (hY : finM V rfl x = Y.1) :
    (Y⁻¹ : GL (Fin V.rank) (EF D)).1 = (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) := by
  have h1 : (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) * Y.1 = 1 := by
    rw [← hY, finM_rfl, ← Matrix.map_mul, ← mt_mul', inv_mul_cancel, mt_one',
      Matrix.map_one _ (map_zero _) (map_one _)]
  calc (Y⁻¹ : GL (Fin V.rank) (EF D)).1
      = ((Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) * Y.1) * (Y⁻¹ : GL (Fin V.rank) (EF D)).1 := by
        rw [h1, Matrix.one_mul]
    _ = (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) := by
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

theorem cong_at_idem : ∀ {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (e : AE D)
    (Ps : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e Ps → ∃ d : ℕ, 0 < d ∧
    ∀ (g : GA D S) (h : GA D T) (Y : GL (Fin a) (EF D)) (Y' : GL (Fin b) (EF D)), finM S hS g = Y.1 → finM T hT h = Y'.1 →
    ∀ (M : ℕ) (γ γ₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T →
      γ₀.map (fun r => e * incA D r) = actO S T g⁻¹ h⁻¹ (γ.map fun r => e * incA D r) + (d * M) • v →
      ∀ P ∈ Ps, ∀ r s, Valued.v (adAt D.host.F P
        ((HMul.hMul (HMul.hMul ((Y'⁻¹ : GL (Fin b) (EF D)).1 : Matrix (Fin b) (Fin b) (EF D))
          (((LinearMap.toMatrix' (toHom S T hS hT γ)).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin b) (Fin a) (EF D))))
          (Y.1 : Matrix (Fin a) (Fin a) (EF D)) -
          ((LinearMap.toMatrix' (toHom S T hS hT γ₀)).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin b) (Fin a) (EF D))) r s)) ≤
        Valued.v ((M : ℕ) : P.adicCompletion D.host.E) := by
  intro D S T a b hS hT e Ps he
  subst hS; subst hT
  obtain ⟨d, hd, hden⟩ := exists_den_stdHom S T
  refine ⟨d, hd, ?_⟩
  intro g h Y Y' hY hY' M γ γ₀ v hv hH P hP r s
  rw [← hY, finM_rfl, inv_val_eq T h Y' hY']
  simp only [toHom, LinearMap.toMatrix'_toLin', finCongr_refl, Matrix.reindex_refl_refl]
  rw [actO, inv_inv] at hH
  have key := read_rel (toEAf D) (adAt D.host.F P) (incA D)
    (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (fun _ => rfl)
    (adAt_toEAf_of_isIdemSum he hP) _ _ γ γ₀ v (d * M) hH r s
  have hint : Valued.v (adAt D.host.F P ((d : EF D) * toEAf D (v r s))) ≤ 1 :=
    (mem_rInt_iff D.host.F D.host.E _).1 (hden v hv r s) P
  rw [RingHom.map_mul, map_natCast (adAt D.host.F P)] at hint
  refine (congrArg Valued.v key).trans_le ?_
  rw [Valuation.map_neg, Nat.cast_mul, mul_right_comm, Valuation.map_mul]
  exact mul_le_of_le_one_left' hint

end GlobalTheory.AdForm.CongAtIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharConjFixed

theorem nontrivial_AF (D : D7) : Nontrivial (AF D.host.F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F))

theorem finrank_AE (D : D7) : Module.finrank (AF D.host.F) (AE D) = 2 := by
  haveI := nontrivial_AF D
  rw [Module.finrank_baseChange]; exact D.sp.cm.deg2

theorem cA_tmul (D : D7) (a : AF D.host.F) (e : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl


set_option synthInstance.maxHeartbeats 200000 in
theorem trace_mem (D : D7) (y : AE D) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y + cA D y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + v, ?_⟩
    rw [map_add (f := _), hu, hv, map_add (f := _)]; abel
  | tmul a e =>
    have hfix : star (e + star e) = e + star e := by
      rw [star_add, star_star, add_comm]
    obtain ⟨f, hf⟩ := (D.sp.cm.fixed _).1 hfix
    refine ⟨f • a, ?_⟩
    rw [cA_tmul, ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one (A := D.host.E) f,
      ← TensorProduct.smul_tmul]
    rfl

theorem fixed_mem (D : D7) (y : AE D) (hy : cA D y = y) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y := by
  obtain ⟨b, hb⟩ := trace_mem D y
  refine ⟨algebraMap D.host.F (AF D.host.F) (2⁻¹) * b, ?_⟩
  have h2 : algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (2⁻¹)) * 2 = 1 := by
    rw [show (2 : AE D) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) 2) by rw [map_ofNat, map_ofNat],
      ← map_mul, ← map_mul, inv_mul_cancel₀ (two_ne_zero : (2 : D.host.F) ≠ 0), map_one, map_one]
  rw [map_mul, hb, hy, ← two_mul, ← mul_assoc, h2, one_mul]

theorem norm_scalar (D : D7) (b : AF D.host.F) :
    Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) b) = b ^ 2 := by
  rw [Algebra.norm_algebraMap, finrank_AE]

theorem fixed_unit (D : D7) (x : (AE D)ˣ) (hx : cA D (x : AE D) = x) :
    ∃ a : (AF D.host.F)ˣ, idF D a = x := by
  obtain ⟨b, hb⟩ := fixed_mem D x hx
  have hn : IsUnit (Algebra.norm (AF D.host.F) (x : AE D)) := x.isUnit.map _
  rw [← hb, norm_scalar] at hn
  obtain ⟨a, ha⟩ := (isUnit_pow_iff two_ne_zero).1 hn
  refine ⟨a, Units.ext ?_⟩
  rw [← hb, ← ha]; rfl

end GlobalTheory.CharConjFixed


open GlobalTheory.CharConjFixed in
theorem GlobalTheory.char_conj_fixed_eq_one : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n →
    ∀ (V : HSp D) (x : (AE D)ˣ), IsDetRoot V 1 x → μ x = 1 := by
  intro D μ n hμ hn V x hx
  have hfix : cA D (x : AE D) = x := by
    have h := hx
    simp only [IsDetRoot, map_one, Units.val_one, Matrix.det_one, one_mul] at h
    exact h.symm
  obtain ⟨a, ha⟩ := fixed_unit D x hfix
  obtain ⟨⟨η, hη⟩, hall⟩ := hμ
  have hμa : μ (idF D a) = η a ^ n := hall η hη a
  have hsq : η a ^ 2 = 1 := by
    rw [← map_pow]
    have : Units.map (↑(Algebra.norm (AF D.host.F)) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := by
      ext
      exact norm_scalar D (a : AF D.host.F)
    rw [← this]; exact hη.2.2.1 _
  obtain ⟨k, rfl⟩ := hn
  rw [← ha, hμa, ← two_mul, pow_mul, hsq, one_pow]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharIntegrable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.PlaceModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocReduction

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T S0 T0 : HSp D} {m n : ℕ}

theorem isHalf_smul {e : AE D} {u : Mx D m n} : IsHalf e u ↔ e • u = u :=
  ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩

theorem heis_add {x y : WO S T} (h : symplO S T x y = 0) (f : WO S T → ℂ) :
    heisO ψ S T (x + y) f = heisO ψ S T x (heisO ψ S T y f) := by
  have := heisL_heisL S T ψ x y f
  rw [symplOH, h, mul_zero, AddChar.map_zero_eq_one, one_smul] at this
  exact this.symm

theorem heis_comm (x y : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y f) = ψ (symplO S T x y) • heisO ψ S T y (heisO ψ S T x f) := heisL_comm S T ψ x y f

theorem heis_smul (x : WO S T) (c : ℂ) (f : WO S T → ℂ) : heisO ψ S T x (c • f) = c • heisO ψ S T x f :=
  (heisL S T ψ x).map_smul c f

section Model

variable {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}

theorem fix_half (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) {u : WO S T} (hu : u ∈ Λ)
    (hu' : IsHalf e u) : heisO ψ S T u f₀ = f₀ := by
  have v1 := h₁.vac
  rw [one_smul] at v1
  rw [← v1, ← h₁.trans _ (GlobalTheory.isSBHalf_halfInd e Λ) u hu']
  congr 1
  funext t
  rw [halfInd_eq_ind]
  exact ind_add _ t (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hu'⟩)

theorem fix_conj (hLL' : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1)
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) {u : WO S T} (hu : u ∈ Λ)
    (hu' : IsHalf (cA D e) u) : heisO ψ S T u f₀ = f₀ := by
  have v1 := h₁.vac
  rw [one_smul] at v1
  rw [← v1, ← h₁.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) u hu']
  congr 1
  funext t
  unfold halfInd
  split_ifs with h
  · rw [hLL' t h.1 h.2 u hu hu', mul_one]
  · rw [mul_zero]

end Model

section Periodic

open GlobalTheory.MixModel

variable {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}

end Periodic

section Red

variable {jA jB : Mx D m n →+ WO S T} {j0 : WO S0 T0 →+ WO S T} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
  (hAA : ∀ a a', symplO S T (jA a) (jA a') = 0) (hA0 : ∀ a z, symplO S T (jA a) (j0 z) = 0)
  (h00 : ∀ z z', symplO S T (j0 z) (j0 z') = symplO S0 T0 z z')
  (hrat : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∃ x, jA γ = ratW T S x) (hcont : Continuous jA)
  (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) 𝓕 μ)

end Red

section Main

variable {jA jB : Mx D m n →+ WO S T} {j0 : WO S0 T0 →+ WO S T} {e : AE D} {Λ : AddSubgroup (WO S T)}
  {Λ0 : AddSubgroup (WO S0 T0)}
  (sA : ∀ (c : AE D) a, jA (c • a) = c • jA a) (sB : ∀ (c : AE D) b, jB (c • b) = c • jB b)
  (s0 : ∀ (c : AE D) z, j0 (c • z) = c • j0 z)
  (hAA : ∀ a a', symplO S T (jA a) (jA a') = 0) (hBB : ∀ b b', symplO S T (jB b) (jB b') = 0)
  (hA0 : ∀ a z, symplO S T (jA a) (j0 z) = 0) (hB0 : ∀ b z, symplO S T (jB b) (j0 z) = 0)
  (h00 : ∀ z z', symplO S T (j0 z) (j0 z') = symplO S0 T0 z z')
  (hdec : ∀ x : WO S T, ∃ a b z, x = jA a + jB b + j0 z)
  (hhalf : ∀ (c : AE D) a b z, IsHalf c (jA a + jB b + j0 z) → IsHalf c a ∧ IsHalf c b ∧ IsHalf c z)
  (hLL' : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1)
  (hX : ∀ x, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ)
  (hY : ∀ y, IsHalf (cA D e) y → (∀ x ∈ Λ, IsHalf e x → ψ (symplO S T x y) = 1) → y ∈ Λ)
  (hsp : ∀ a b z, IsHalf e a → IsHalf e b → IsHalf e z →
    (jA a + jB b + j0 z ∈ Λ ↔ jA a ∈ Λ ∧ jB b ∈ Λ ∧ j0 z ∈ Λ))
  (hsp0 : ∀ z, IsHalf e z → (j0 z ∈ Λ ↔ z ∈ Λ0))

variable {μw : Measure (Mx D m n)} (hψ : IsStdChar D ψ (-1)) (hcont : Continuous jA)
  (hcl : IsClosed {x : WO S T | x ∈ Λ ∧ IsHalf e x})
  (hw0 : μw {a | ¬ IsHalf e a} = 0) (hw1 : ∀ a₀ : Mx D m n, IsHalf e a₀ → Measure.map (fun a => a + a₀) μw = μw)
  (hw2 : μw {a | IsHalf e a ∧ jA a ∈ Λ} = 1)

variable {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
  (hrat : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∃ x, jA γ = ratW T S x)
  (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) 𝓕 μ)
  (hec : e * cA D e = 0) (hinf : infPart D e = 0)
  {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hf₀ : IsThetaFunO ψ S T f₀)
  (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)

end Main

section Lattice

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {e : AE D}


open GlobalTheory.PlaceDatum in
theorem lattice_facts (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (he : e * e = e)
    (hinf : infPart D e = 0) :
    (∀ u ∈ latO S T ΛS ΛT fun _ => True, IsHalf e u → ∀ y ∈ latO S T ΛS ΛT fun _ => True, IsHalf (cA D e) y →
      ψ (symplO S T u y) = 1) ∧
    (∀ x, IsHalf e x → (∀ y ∈ latO S T ΛS ΛT fun _ => True, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) →
      x ∈ latO S T ΛS ΛT fun _ => True) ∧
    (∀ y, IsHalf (cA D e) y → (∀ x ∈ latO S T ΛS ΛT fun _ => True, IsHalf e x → ψ (symplO S T x y) = 1) →
      y ∈ latO S T ΛS ΛT fun _ => True) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∃ r ∈ R, ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u) ∧
    ∀ y, IsHalf (cA D e) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ latO S T ΛS ΛT fun _ => True := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  refine ⟨fun u hu hu' y hy _ => (hdual u (infPart_of_half hinf hu')).1 hu y hy, fun x hx h => ?_, fun y hy h => ?_,
    fun k hk => ?_, fun y hy => exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) hy)⟩
  · refine (hdual x (infPart_of_half hinf hx)).2 fun u hu => ?_
    have := h _ (hsm _ he' u hu).1 ((isHalf_iff S T).2 (hsm _ he' u hu).2)
    rwa [← symplO_smul, isHalf_smul.1 hx] at this
  · refine (hdual y (infPart_of_half (infPart_cA hinf) hy)).2 fun u hu => ?_
    have := h _ (hsm _ he u hu).1 ((isHalf_iff S T).2 (hsm _ he u hu).2)
    rw [symplO_smul, isHalf_smul.1 hy] at this
    rw [symplO_skew, ← one_mul (ψ _), ← this, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, this]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

end Lattice

end GlobalTheory.LocReduction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Transport

def CongAt (B : Base) {a b : ℕ} (P : HeightOneSpectrum (𝓞 B.host.E)) (M₀ : ℕ) (y : TC.GA B a) (y' : TC.GA B b)
    (x x₀ : Formalism.L2.Col.HomE B.fields.E a b) : Prop :=
  ∀ r s, Valued.v (adAt B.host.F P
    ((HMul.hMul (HMul.hMul ((y'⁻¹ : TC.GA B b).1 : Matrix (Fin b) (Fin b) (Formalism.L2.DIV.AfE B.host.F B.host.E))
      ((LinearMap.toMatrix' x).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E)))
      (y.1 : Matrix (Fin a) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E)) -
      ((LinearMap.toMatrix' x₀).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E))) r s)) ≤
    Valued.v ((M₀ : ℕ) : P.adicCompletion B.host.E)

end GlobalTheory.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralNegligibleOrbitsEqZeroCuspFormStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_integral_negligible_orbits_eq_zero_cuspForm : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' q : {q : GlobalTheory.Eis.SiegelCosets V // ¬ ∃ δ ∈ GQ V, ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V}, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = 0 := by
  first | exact @GlobalTheory.Core.Rk.NegOrbit.integral_neg_eq_zero | exact GlobalTheory.Core.Rk.NegOrbit.integral_neg_eq_zero | (intros; apply GlobalTheory.Core.Rk.NegOrbit.integral_neg_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlaceStatement
section
alias GlobalTheory.T.threeOrbits_gluedCore_atPlace := GlobalTheory.FinPl.orbitGlued
end

