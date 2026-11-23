module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTermOfIsotropic
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open Polynomial NumberField
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

noncomputable section

namespace GlobalTheory.CompanionTheory.EllIso

theorem exists_eigvec {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) (hS : S ≠ ⊥)
    (hst : ∀ x ∈ S, G *ᵥ x ∈ S) : ∃ (z : ℂ) (v : Fin n → ℂ), v ∈ S ∧ v ≠ 0 ∧ G *ᵥ v = z • v := by
  haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS
  let f : Module.End ℂ S := (Matrix.toLin' G).restrict (fun x hx => by simpa using hst x hx)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, v, v.2, fun h => hv.2 (Subtype.ext h), ?_⟩
  have := congrArg Subtype.val hv.apply_eq_smul
  simpa [f] using this

theorem eig_line {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hs : G.charpoly.Separable) (z : ℂ) (v u : Fin n → ℂ)
    (hv : v ≠ 0) (hGv : G *ᵥ v = z • v) (hGu : G *ᵥ u = z • u) : ∃ c : ℂ, u = c • v := by
  let f : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' G
  have hfc : LinearMap.charpoly f = G.charpoly := by
    simp [f, Matrix.charpoly_toLin']
  have hmem : ∀ w, G *ᵥ w = z • w → w ∈ Module.End.eigenspace f z := fun w hw => by
    rw [Module.End.mem_eigenspace_iff]; simpa [f] using hw
  have h1 : Module.finrank ℂ (Module.End.eigenspace f z) ≤ 1 := by
    have a := Submodule.finrank_mono (Module.End.eigenspace_le_maxGenEigenspace (f := f) (μ := z))
    have b := LinearMap.finrank_maxGenEigenspace_eq f z
    rw [hfc] at b
    have c := Polynomial.rootMultiplicity_le_one_of_separable hs z
    omega
  let v' : Module.End.eigenspace f z := ⟨v, hmem v hGv⟩
  let u' : Module.End.eigenspace f z := ⟨u, hmem u hGu⟩
  have hv' : v' ≠ 0 := fun h => hv (congrArg Subtype.val h)
  have h2 : Module.finrank ℂ (Module.End.eigenspace f z) = 1 := by
    haveI : Nontrivial (Module.End.eigenspace f z) := ⟨v', 0, hv'⟩
    have := Module.finrank_pos (R := ℂ) (M := Module.End.eigenspace f z)
    omega
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v' hv').1 h2 u'
  exact ⟨c, (congrArg Subtype.val hc).symm⟩


open ComplexOrder in
theorem iso_bot_C {n : ℕ} (G B Bi : Matrix (Fin n) (Fin n) ℂ) (hB : B * Bi = 1) (hinv : Gᴴ * B * G = B)
    (hs : G.charpoly.Separable) (hz : ∀ z, G.charpoly.IsRoot z → ‖z‖ = 1) (S : Submodule ℂ (Fin n → ℂ))
    (hst : ∀ x ∈ S, G *ᵥ x ∈ S) (hiso : ∀ x ∈ S, ∀ y ∈ S, star x ⬝ᵥ (B *ᵥ y) = 0) : S = ⊥ := by
  by_contra hS
  obtain ⟨z, v, hvS, hv0, hGv⟩ := exists_eigvec G S hS hst
  have hroot : G.charpoly.IsRoot z := by
    have : (Matrix.scalar (Fin n) z - G).det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, ?_⟩
      rw [Matrix.sub_mulVec, hGv]
      simp [Matrix.scalar_apply, Matrix.smul_mulVec]
    rw [Polynomial.IsRoot, Matrix.eval_charpoly]
    exact this
  have hz1 : star z * z = 1 := by
    have h := hz z hroot
    have : (starRingEnd ℂ) z * z = ((Complex.normSq z : ℝ) : ℂ) := by rw [mul_comm]; exact Complex.mul_conj z
    rw [Complex.normSq_eq_norm_sq, h] at this
    simpa using this
  let l : (Fin n → ℂ) → ℂ := fun y => star v ⬝ᵥ (B *ᵥ y)
  have hladd : ∀ a b, l (a + b) = l a + l b := fun a b => by simp [l, Matrix.mulVec_add, dotProduct_add]
  have hlsmul : ∀ (c : ℂ) a, l (c • a) = c * l a := fun c a => by
    simp [l, Matrix.mulVec_smul, dotProduct_smul]
  have hlG : ∀ y, l (G *ᵥ y) = z * l y := fun y => by
    have h0 : star (G *ᵥ v) ⬝ᵥ (B *ᵥ (G *ᵥ y)) = star v ⬝ᵥ (B *ᵥ y) := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinv]
    rw [hGv, star_smul, smul_dotProduct] at h0
    have h1 : star z * l (G *ᵥ y) = l y := by simpa [l] using h0
    calc l (G *ᵥ y) = z * (star z * l (G *ᵥ y)) := by
          rw [← mul_assoc, mul_comm z, hz1, one_mul]
      _ = z * l y := by rw [h1]
  have hpoly : ∀ (f : ℂ[X]) y, l (aeval G f *ᵥ y) = f.eval z * l y := by
    intro f
    induction f using Polynomial.induction_on' with
    | add p q hp hq =>
      intro y
      rw [map_add (f := _), Matrix.add_mulVec, hladd, hp, hq, Polynomial.eval_add, add_mul]
    | monomial k a =>
      induction k with
      | zero =>
        intro y
        simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, hlsmul]
      | succ k ih =>
        intro y
        have e : aeval G (monomial (k + 1) a) = aeval G (monomial k a) * G := by
          simp [Polynomial.aeval_monomial, pow_succ, mul_assoc]
        rw [e, ← Matrix.mulVec_mulVec, ih, hlG]
        simp [pow_succ]
        ring
  obtain ⟨q, hq⟩ : (X - C z) ∣ G.charpoly := Polynomial.dvd_iff_isRoot.2 hroot
  have hqz : q.eval z ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.2 h0
    have h2 : (X - C z) ^ 2 ∣ G.charpoly := ⟨r, by rw [hq, hr]; ring⟩
    have h3 := (Polynomial.le_rootMultiplicity_iff hs.ne_zero).2 h2
    have h4 := Polynomial.rootMultiplicity_le_one_of_separable hs z
    omega
  have hl0 : ∀ y, l y = 0 := by
    intro y
    have h1 : G *ᵥ (aeval G q *ᵥ y) = z • (aeval G q *ᵥ y) := by
      have h0 : aeval G ((X - C z) * q) = 0 := by rw [← hq]; exact Matrix.aeval_self_charpoly G
      rw [map_mul, map_sub, aeval_X, aeval_C, sub_mul] at h0
      have h2 := congrArg (fun M => M *ᵥ y) h0
      simp only [Matrix.sub_mulVec, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec] at h2
      rw [sub_eq_zero] at h2
      rw [h2]
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    obtain ⟨c, hc⟩ := eig_line G hs z v _ hv0 hGv h1
    have h3 : q.eval z * l y = 0 := by
      rw [← hpoly, hc, hlsmul]
      have : l v = 0 := hiso v hvS v hvS
      rw [this, mul_zero]
    exact (mul_eq_zero.1 h3).resolve_left hqz
  apply hv0
  have h5 : star v = 0 := by
    apply dotProduct_eq_zero
    intro w
    have h := hl0 (Bi *ᵥ w)
    simpa only [l, Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using h
  simpa using congrArg star h5

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem nrm_map (τ : E →+* ℂ) (d : GL (Fin n) E) :
    (nrm d).val.map τ = d.val.map τ * ((d⁻¹ : GL (Fin n) E).val.map τ)ᴴ := by
  have e : (thetaE E n d).val.map τ = ((d⁻¹ : GL (Fin n) E).val.map τ)ᴴ := by
    rw [thetaE, thetaR_val]
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    exact NumberField.IsCMField.complexEmbedding_complexConj E τ _
  rw [nrm, Units.val_mul, Matrix.map_mul, e]

theorem iso_bot (d : GL (Fin n) E) (hd : IsRegEll d) (W : Submodule E (Fin n → E)) (hW : img (nrm d) W = W)
    (hi : W ≤ perpD (conjE E) d W) : W = ⊥ := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  set A := d.val.map τ with hA
  set Ai := (d⁻¹ : GL (Fin n) E).val.map τ with hAi
  have hAA : Ai * A = 1 := by
    rw [hA, hAi, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel]
    simp [Matrix.map_one]
  have hAA' : A * Ai = 1 := by
    rw [hA, hAi, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel]
    simp [Matrix.map_one]
  set G := (nrm d).val.map τ with hG
  have hGe : G = A * Aiᴴ := nrm_map τ d
  have hinv : Gᴴ * Ai * G = Ai := by
    have h1 : Aᴴ * Aiᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hAA, Matrix.conjTranspose_one]
    rw [hGe, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Ai * Aᴴ * Ai * (A * Aiᴴ) = Ai * Aᴴ * (Ai * A) * Aiᴴ := by simp only [Matrix.mul_assoc]
      _ = Ai * (Aᴴ * Aiᴴ) := by rw [hAA, Matrix.mul_one, Matrix.mul_assoc]
      _ = Ai := by rw [h1, Matrix.mul_one]
  have hcp : G.charpoly = (nrm d).val.charpoly.map τ := Matrix.charpoly_map _ _
  have hs : G.charpoly.Separable := by rw [hcp]; exact hd.1.map
  have hz : ∀ z, G.charpoly.IsRoot z → ‖z‖ = 1 := fun z h => hd.2 τ z (hcp ▸ h)
  let S : Submodule ℂ (Fin n → ℂ) := Submodule.span ℂ ((fun w : Fin n → E => τ ∘ w) '' (W : Set (Fin n → E)))
  have hgen : ∀ w ∈ W, τ ∘ w ∈ S := fun w hw => Submodule.subset_span ⟨w, hw, rfl⟩
  have hstab : ∀ w ∈ W, (nrm d).val *ᵥ w ∈ W := fun w hw => by
    have : (nrm d).val *ᵥ w ∈ img (nrm d) W := ⟨w, hw, rfl⟩
    rwa [hW] at this
  have hst : ∀ x ∈ S, G *ᵥ x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨w, hw, rfl⟩ := h
      have : G *ᵥ (τ ∘ w) = τ ∘ ((nrm d).val *ᵥ w) := by
        funext i
        exact (RingHom.map_mulVec τ _ _ i).symm
      rw [this]
      exact hgen _ (hstab w hw)
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact S.add_mem ha hb
    | smul c a _ ha => rw [Matrix.mulVec_smul]; exact S.smul_mem c ha
  have hbase : ∀ x ∈ W, ∀ y ∈ W, star (τ ∘ x) ⬝ᵥ (Ai *ᵥ (τ ∘ y)) = 0 := by
    intro x hx y hy
    obtain ⟨y', hy', hyy⟩ := hi hy
    have hy2 : (d⁻¹ : GL (Fin n) E).val *ᵥ y = y' := by
      rw [← hyy]
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    have h0 : ∑ i, conjE E (x i) * y' i = 0 := hy' x hx
    have h1 : Ai *ᵥ (τ ∘ y) = τ ∘ y' := by
      funext i
      rw [← hy2]
      exact (RingHom.map_mulVec τ _ _ i).symm
    rw [h1]
    have h2 := congrArg τ h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h2
    rw [← h2]
    simp only [dotProduct, Pi.star_apply, Function.comp_apply, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact (NumberField.IsCMField.complexEmbedding_complexConj E τ _).symm
  have hiso : ∀ x ∈ S, ∀ y ∈ S, star x ⬝ᵥ (Ai *ᵥ y) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, ha, rfl⟩ := h
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y h =>
        obtain ⟨b, hb, rfl⟩ := h
        exact hbase a ha b hb
      | zero => simp
      | add p q _ _ hp hq => rw [Matrix.mulVec_add, dotProduct_add, hp, hq, add_zero]
      | smul c p _ hp => rw [Matrix.mulVec_smul, dotProduct_smul, hp, smul_zero]
    | zero => intro y _; simp
    | add p q _ _ hp hq =>
      intro y hy
      rw [star_add, add_dotProduct, hp y hy, hq y hy, add_zero]
    | smul c p _ hp =>
      intro y hy
      rw [star_smul, smul_dotProduct, hp y hy, smul_zero]
  have hS := iso_bot_C G Ai A hAA hinv hs hz S hst hiso
  rw [Submodule.eq_bot_iff]
  intro w hw
  have h1 : τ ∘ w = 0 := by
    have := hgen w hw
    rw [hS] at this
    exact (Submodule.mem_bot ℂ).1 this
  funext i
  exact τ.injective (by simpa using congrFun h1 i)

theorem deg_bot (x : GA E n) : deg x (⊥ : Submodule E (Fin n → E)) = 0 := by
  have key : ∀ (k : ℕ) (_ : k = 0) (M : Matrix (Fin n) (Fin k) E), degM x M = 0 := by
    rintro k rfl M
    exact degM_zero x M
  exact key _ (by simp) _

theorem ellTerm_of_onlyIsotropic : OnlyIsotropic → EllTerm := by
  intro h E _ _ _ n
  obtain ⟨C, hC⟩ := h E n
  refine ⟨C, fun τ x d hd hτ => (hC τ x d hτ).2 fun W hW hi => ?_⟩
  obtain rfl := iso_bot d hd W hW hi
  rw [deg_bot]
  simp [prof]

end GlobalTheory.CompanionTheory.EllIso

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompatibleFamilyOfSingleton
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_compatible_family_of_singleton : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ (i : ι) (f : P {i}), ∃ (c : ∀ j : ι, P {j}) (N : ℕ), (∀ j l, res {j} {j, l} (sub_pair_left j l) (c j) = res {l} {j, l} (sub_pair_right j l) (c l)) ∧ c i = (MvPolynomial.X i : MvPolynomial ι A) ^ N • f) := by
  intro ι _ _ A _ P _ _ res hid hcomp hker hext i f
  have inj : ∀ (S S' : Finset ι) (h : S ⊆ S'), S = S' → Function.Injective (res S S' h) := by
    rintro S _ h rfl a b hab
    rwa [hid, hid] at hab
  set x : MvPolynomial ι A := MvPolynomial.X i with hx

  have h1 : ∀ j : ι, ∃ (k : ℕ) (g : P {j}),
      res {j} {i, j} (sub_pair_right i j) g = x ^ k • res {i} {i, j} (sub_pair_left i j) f := by
    intro j
    obtain ⟨k, g, hg⟩ := hext {j} i (res {i} {i, j} (sub_pair_left i j) f)
      (Finset.singleton_nonempty j)
    exact ⟨k, g, hg⟩
  choose k g hg using h1
  set K : ℕ := Finset.univ.sup k with hK
  have hkK : ∀ j, k j ≤ K := fun j => Finset.le_sup (Finset.mem_univ j)
  obtain ⟨f', hres⟩ : ∃ f' : ∀ j : ι, P {j}, ∀ j, res {j} {i, j} (sub_pair_right i j) (f' j)
      = x ^ K • res {i} {i, j} (sub_pair_left i j) f := by
    refine ⟨fun j => x ^ (K - k j) • g j, fun j => ?_⟩
    simp only [map_smul, hg, smul_smul, ← pow_add, Nat.sub_add_cancel (hkK j)]

  have htriple : ∀ (j : ι) (T : Finset ι) (hT : ({i, j} : Finset ι) ⊆ T),
      res {j} T ((sub_pair_right i j).trans hT) (f' j)
        = x ^ K • res {i} T ((sub_pair_left i j).trans hT) f := by
    intro j T hT
    rw [← hcomp _ _ _ (sub_pair_right i j) hT, hres, map_smul, hcomp]
  have h2 : ∀ j l : ι, ∃ n : ℕ, x ^ n • (res {j} {j, l} (sub_pair_left j l) (f' j)
      - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0 := by
    intro j l
    refine hker {j, l} i _ (Finset.insert_nonempty _ _) ?_
    have hj : ({i, j} : Finset ι) ⊆ insert i {j, l} :=
      Finset.insert_subset_insert i (sub_pair_left j l)
    have hl : ({i, l} : Finset ι) ⊆ insert i {j, l} :=
      Finset.insert_subset_insert i (sub_pair_right j l)
    rw [map_sub, hcomp, hcomp, sub_eq_zero]
    have e1 := htriple j _ hj
    have e2 := htriple l _ hl
    exact e1.trans e2.symm
  choose n hn using h2
  set N' : ℕ := Finset.univ.sup (fun p : ι × ι => n p.1 p.2) with hN'
  have hnN : ∀ j l, n j l ≤ N' := fun j l =>
    Finset.le_sup (f := fun p : ι × ι => n p.1 p.2) (Finset.mem_univ (j, l))
  refine ⟨fun j => x ^ N' • f' j, N' + K, ?_, ?_⟩
  · intro j l
    have h0 : x ^ N' • (res {j} {j, l} (sub_pair_left j l) (f' j)
        - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0 := by
      rw [← Nat.sub_add_cancel (hnN j l), pow_add, mul_smul, hn, smul_zero]
    show res {j} {j, l} (sub_pair_left j l) (x ^ N' • f' j)
      = res {l} {j, l} (sub_pair_right j l) (x ^ N' • f' l)
    rw [map_smul, map_smul, ← sub_eq_zero, ← smul_sub]
    exact h0
  · have hii : ({i} : Finset ι) ⊆ {i, i} := sub_pair_left i i
    have hfi : f' i = x ^ K • f := by
      apply inj {i} {i, i} hii (Finset.pair_eq_singleton i).symm
      rw [map_smul]
      exact hres i
    show x ^ N' • f' i = x ^ (N' + K) • f
    rw [hfi, smul_smul, ← pow_add]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsometryFlagOfEquiv
section
noncomputable section

open Matrix Module PositivityTheory.Rg.BcB

namespace GlobalTheory.CompanionTheory.IwaDecomp

section Isometry

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

def isoOfFinrank (h : finrank ℂ F = finrank ℂ G) : F ≃ₗᵢ[ℂ] G :=
  (stdOrthonormalBasis ℂ F).equiv (stdOrthonormalBasis ℂ G) (finCongr h)

theorem exists_extend (h : finrank ℂ F = finrank ℂ G) (S : Submodule ℂ F) (φ : S →ₗᵢ[ℂ] G) :
    ∃ ψ : F →ₗᵢ[ℂ] G, ∀ s : S, ψ s = φ s := by
  let e := isoOfFinrank h
  let L : S →ₗᵢ[ℂ] F := e.symm.toLinearIsometry.comp φ
  refine ⟨e.toLinearIsometry.comp L.extend, fun s => ?_⟩
  simp [L, LinearIsometry.extend_apply]

theorem finrank_map_isometry (K : E →ₗᵢ[ℂ] E) (A : Submodule ℂ E) :
    finrank ℂ (A.map K.toLinearMap) = finrank ℂ A :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective K.toLinearMap K.injective A)).symm

theorem exists_isometry_flag {A₁ A₂ B₁ B₂ : Submodule ℂ E} (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (h₁ : finrank ℂ A₁ = finrank ℂ B₁) (h₂ : finrank ℂ A₂ = finrank ℂ B₂) :
    ∃ K : E →ₗᵢ[ℂ] E, A₁.map K.toLinearMap = B₁ ∧ A₂.map K.toLinearMap = B₂ := by
  let φ : A₁ ≃ₗᵢ[ℂ] B₁ := isoOfFinrank h₁
  let S : Submodule ℂ A₂ := A₁.comap A₂.subtype
  let ι : S →ₗᵢ[ℂ] A₁ :=
    ⟨LinearMap.codRestrict A₁ (A₂.subtype ∘ₗ S.subtype) (fun x => x.2), fun x => rfl⟩
  let j : B₁ →ₗᵢ[ℂ] B₂ := ⟨Submodule.inclusion hB, fun x => rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_extend h₂ S (j.comp (φ.toLinearIsometry.comp ι))
  let L : A₂ →ₗᵢ[ℂ] E := B₂.subtypeₗᵢ.comp ψ
  have hK : ∀ a : A₂, L.extend a = ψ a := fun a => by
    simpa [L] using LinearIsometry.extend_apply L a
  refine ⟨L.extend, ?_, ?_⟩
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₁)
    rintro _ ⟨a, ha, rfl⟩
    have h := hK ⟨a, hA ha⟩
    have h2 := hψ ⟨⟨a, hA ha⟩, ha⟩
    change L.extend a ∈ B₁
    rw [show L.extend a = ((ψ ⟨a, hA ha⟩ : B₂) : E) from h, show ψ ⟨a, hA ha⟩ = _ from h2]
    exact (φ (ι ⟨⟨a, hA ha⟩, ha⟩)).2
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₂)
    rintro _ ⟨a, ha, rfl⟩
    change L.extend a ∈ B₂
    rw [show L.extend a = ((ψ ⟨a, ha⟩ : B₂) : E) from hK ⟨a, ha⟩]
    exact (ψ ⟨a, ha⟩).2

theorem exists_isometry_flag_of_equiv {V : Type*} [AddCommGroup V] [Module ℂ V] (e : V ≃ₗ[ℂ] E)
    {A₁ A₂ B₁ B₂ : Submodule ℂ V} (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (h₁ : finrank ℂ A₁ = finrank ℂ B₁) (h₂ : finrank ℂ A₂ = finrank ℂ B₂) :
    ∃ K : E →ₗᵢ[ℂ] E, (A₁.map (e : V →ₗ[ℂ] E)).map K.toLinearMap = B₁.map (e : V →ₗ[ℂ] E) ∧
      (A₂.map (e : V →ₗ[ℂ] E)).map K.toLinearMap = B₂.map (e : V →ₗ[ℂ] E) := by
  have hT : ∀ W : Submodule ℂ V, finrank ℂ (W.map (e : V →ₗ[ℂ] E)) = finrank ℂ W :=
    fun W => LinearEquiv.finrank_map_eq e W
  exact exists_isometry_flag (Submodule.map_mono hA) (Submodule.map_mono hB)
    (by rw [hT, hT, h₁]) (by rw [hT, hT, h₂])

end Isometry

variable {n : ℕ}

theorem img_one (W : Submodule ℂ (Fin n → ℂ)) : img (1 : GL (Fin n) ℂ) W = W := by
  simp [img]

theorem img_mul (a b : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : img (a * b) W = img a (img b W) := by
  simp only [img, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem img_mono (a : GL (Fin n) ℂ) {W W' : Submodule ℂ (Fin n → ℂ)} (h : W ≤ W') : img a W ≤ img a W' :=
  Submodule.map_mono h

def linEquiv (g : GL (Fin n) ℂ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.toLin'OfInv (M := (g⁻¹ : GL (Fin n) ℂ).val) (M' := g.val) (by simp) (by simp)

theorem img_eq_map_linEquiv (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    img g W = W.map (linEquiv g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
  rfl

theorem finrank_img (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : finrank ℂ (img g W) = finrank ℂ W := by
  rw [img_eq_map_linEquiv]
  exact LinearEquiv.finrank_map_eq (linEquiv g) W

theorem thetaR_eq_self_iff (k : GL (Fin n) ℂ) :
    thetaR (starRingEnd ℂ) n k = k ↔ k.val.conjTranspose = (k⁻¹ : GL (Fin n) ℂ).val := by
  have h : (thetaR (starRingEnd ℂ) n k).val = (k⁻¹ : GL (Fin n) ℂ).val.conjTranspose := by
    rw [thetaR_val]; ext i j; simp [Matrix.conjTranspose_apply]
  constructor
  · intro e
    have h' := congrArg Units.val e
    rw [h] at h'
    rw [← h', Matrix.conjTranspose_conjTranspose]
  · intro e
    refine Units.ext ?_
    rw [h, ← e, Matrix.conjTranspose_conjTranspose]

abbrev eu (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm

theorem unitary_of_isometry (K : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    ∃ k : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n k = k ∧
      ∀ W : Submodule ℂ (Fin n → ℂ), (img k W).map (eu n : (Fin n → ℂ) →ₗ[ℂ] _) =
        (W.map (eu n : (Fin n → ℂ) →ₗ[ℂ] _)).map K.toLinearMap := by
  let f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    ((eu n).symm : _ →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ K.toLinearMap ∘ₗ (eu n : (Fin n → ℂ) →ₗ[ℂ] _)
  let M : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' f
  have hM : Matrix.toLin' M = f := Matrix.toLin'_toMatrix' f
  have key : ∀ x y : Fin n → ℂ, f y ⬝ᵥ star (f x) = y ⬝ᵥ star x := fun x y => by
    have := K.inner_map_map (eu n x) (eu n y)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at this
    exact this
  have hc : ∀ i l, M l i = f (Pi.single i 1) l := fun i l => by
    rw [← hM, Matrix.toLin'_apply, Matrix.mulVec_single_one]
    rfl
  have h1 : M.conjTranspose * M = 1 := by
    ext i j
    have h := key (Pi.single i 1) (Pi.single j 1)
    have e : (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ star (Pi.single i 1 : Fin n → ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
      rw [single_one_dotProduct]
      simp [Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [← e, ← h]
    simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, hc, Pi.star_apply, mul_comm]
  have h2 : M * M.conjTranspose = 1 := mul_eq_one_comm.1 h1
  let k : GL (Fin n) ℂ := ⟨M, M.conjTranspose, h2, h1⟩
  refine ⟨k, (thetaR_eq_self_iff k).2 rfl, fun W => ?_⟩
  have : (k.val : Matrix (Fin n) (Fin n) ℂ) = M := rfl
  change Submodule.map _ (Submodule.map (Matrix.toLin' M) W) = _
  rw [hM, ← Submodule.map_comp, ← Submodule.map_comp]
  refine congrArg (fun t => Submodule.map t W) (LinearMap.ext fun x => ?_)
  simp [f]

theorem img_mul_inv_eq {g k : GL (Fin n) ℂ} {W : Submodule ℂ (Fin n → ℂ)} (h : img k (img g⁻¹ W) = W) :
    img (g * k⁻¹) W = W := by
  conv_lhs => rw [← h]
  rw [← img_mul, ← img_mul, show g * k⁻¹ * k * g⁻¹ = 1 by group, img_one]

theorem exists_flag_unitary (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (h : W₁ ≤ W₂) (g : GL (Fin n) ℂ) :
    ∃ k : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n k = k ∧ img k (img g⁻¹ W₁) = W₁ ∧ img k (img g⁻¹ W₂) = W₂ := by
  obtain ⟨K, hK₁, hK₂⟩ := exists_isometry_flag_of_equiv (eu n) (img_mono g⁻¹ h) h
    (finrank_img g⁻¹ W₁) (finrank_img g⁻¹ W₂)
  obtain ⟨k, hk, hkK⟩ := unitary_of_isometry K
  have hinj : Function.Injective (eu n : (Fin n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := (eu n).injective
  have inj := Submodule.map_injective_of_injective hinj
  exact ⟨k, hk, inj ((hkK _).trans hK₁), inj ((hkK _).trans hK₂)⟩

theorem exists_eq_mul_unitary (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (h : W₁ ≤ W₂) (g : GL (Fin n) ℂ) :
    ∃ q k : GL (Fin n) ℂ, g = q * k ∧ thetaR (starRingEnd ℂ) n k = k ∧ img q W₁ = W₁ ∧ img q W₂ = W₂ := by
  obtain ⟨k, hk, h₁, h₂⟩ := exists_flag_unitary W₁ W₂ h g
  exact ⟨g * k⁻¹, k, by group, hk, img_mul_inv_eq h₁, img_mul_inv_eq h₂⟩

theorem iwaFlag : PositivityTheory.Rg.BcB.D4.IwaFlag := fun _ W₁ W₂ h g => by
  obtain ⟨q, k, e, hk, h₁, h₂⟩ := exists_eq_mul_unitary W₁ W₂ h g
  exact ⟨q, ⟨h₁, h₂⟩, k, hk, e⟩

end GlobalTheory.CompanionTheory.IwaDecomp
end
end

