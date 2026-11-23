module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0051

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BoxSumNeZeroInvariantAffineChange
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange

open GlobalTheory.Proof.NormalFormAtPrime

theorem relIndex_ne_zero_of_cover {V : Type} [AddCommGroup V] (H K : AddSubgroup V) (S : Finset V)
    (h : ∀ k ∈ K, ∃ s ∈ S, k - s ∈ H) : H.relIndex K ≠ 0 := by
  rw [← QuotientAddGroup.ker_mk' H, AddSubgroup.relIndex_ker]
  have hf : ((K.map (QuotientAddGroup.mk' H) : AddSubgroup (V ⧸ H)) : Set (V ⧸ H)).Finite := by
    refine (S.finite_toSet.image (QuotientAddGroup.mk' H)).subset ?_
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨s, hs, e⟩ := h k hk
    exact ⟨s, hs, (QuotientAddGroup.eq_iff_sub_mem.2 e).symm⟩
  have : Finite (K.map (QuotientAddGroup.mk' H)) := hf
  exact Nat.card_pos.ne'

variable {E : Type} [Field E] [NumberField E]

def lat (P : HeightOneSpectrum (𝓞 E)) (ι : Type) (c : E) : AddSubgroup (ι → E) where
  carrier := {u | ∀ i, IntAt P (c * u i)}
  zero_mem' := fun i => by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
  add_mem' := fun {a b} ha hb i => by
    have := (ha i).add (hb i)
    rwa [← mul_add] at this
  neg_mem' := fun {a} ha i => by
    have := IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (ha i)
    simpa using this

theorem lat_le {P : HeightOneSpectrum (𝓞 E)} {ι : Type} {c c' : E} (k : ℕ) (h : c' = (qOf P : E) ^ k * c) :
    lat P ι c ≤ lat P ι c' := fun u hu i => by
  rw [h, mul_assoc]
  exact intAt_pow_mul k (hu i)

theorem exists_fin {P : HeightOneSpectrum (𝓞 E)} (h : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x))
    {κ : Type} [Fintype κ] (x : κ → E) : ∃ m : ℕ, ∀ m', m ≤ m' → ∀ k, IntAt P ((qOf P : E) ^ m' * x k) := by
  choose m hm using h
  refine ⟨Finset.univ.sup fun k => m (x k), fun m' hm' k => intAt_pow_mono (le_trans ?_ hm') (hm (x k))⟩
  exact Finset.le_sup (f := fun k => m (x k)) (Finset.mem_univ k)

theorem exists_bound {P : HeightOneSpectrum (𝓞 E)} (h : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x))
    {ι : Type} [Fintype ι] [DecidableEq ι] (T : (ι → E) →ₗ[E] (ι → E)) :
    ∃ m : ℕ, ∀ m', m ≤ m' → ∀ (c : E) (u : ι → E), u ∈ lat P ι c → T u ∈ lat P ι ((qOf P : E) ^ m' * c) := by
  obtain ⟨m, hm⟩ := exists_fin h (fun p : ι × ι => T (Pi.single p.1 1) p.2)
  refine ⟨m, fun m' hm' c u hu l => ?_⟩
  have e : T u = ∑ s, u s • T (Pi.single s 1) := by
    conv_lhs => rw [show u = ∑ s, u s • (Pi.single s (1 : E) : ι → E) from by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e, Finset.sum_apply, Finset.mul_sum]
  refine intAt_sum _ _ fun s _ => ?_
  have := (hu s).mul (hm m' hm' (s, l))
  convert this using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem affine : (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y)) → (∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0)) → (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s))) → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E), ∃ A₀ B₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → B₀ ≤ B → (boxSum P A B (fun t => f (T t + b)) ≠ 0 ↔ boxSum P A B f ≠ 0) := by
  classical
  intro h1 h2 h3 E _ _ K _ _ P hP ι _ _ f N hf T b
  have hq := qOf_ne_zero P
  have hs : ∀ x : E, ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * x) := fun x => by
    obtain ⟨m, hm⟩ := (h1 E P 1 1).1 (fun _ => x)
    exact ⟨m, hm m le_rfl 0⟩
  have sep : ∀ A B : ℕ, ∀ s ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B),
      ∀ s' ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B),
      s - s' ∈ lat P ι ((qOf P : E) ^ B)⁻¹ → s = s' := fun A B s hs s' hs' h => by
    funext i
    exact (h3 E P hP A B).1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i)
  have cov : ∀ A B : ℕ, ∀ v ∈ lat P ι ((qOf P : E) ^ A),
      ∃ s ∈ Fintype.piFinset (fun _ : ι => LocE.valsQ E (qOf P) A B), v - s ∈ lat P ι ((qOf P : E) ^ B)⁻¹ :=
    fun A B v hv => by
      choose s hs hs' using fun i => (h3 E P hP A B).2 (v i) (hv i)
      exact ⟨s, Fintype.mem_piFinset.2 hs, hs'⟩
  have inv : ∀ v, ∀ u ∈ lat P ι ((qOf P : E) ^ N)⁻¹, f (v + u) = f v := fun v u hu => by
    have := hf.2 v (((qOf P : E) ^ N)⁻¹ • u) hu
    rwa [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul] at this
  obtain ⟨m1, hm1⟩ := exists_bound hs T.toLinearMap
  obtain ⟨m2, hm2⟩ := exists_bound hs T.symm.toLinearMap
  obtain ⟨m3, hm3⟩ := exists_fin hs b
  obtain ⟨m, a1, a2, a3⟩ : ∃ m, m1 ≤ m ∧ m2 ≤ m ∧ m3 ≤ m := ⟨m1 + m2 + m3, by omega, by omega, by omega⟩
  have hT := hm1 m a1
  have hT' := hm2 m a2
  have hb : b ∈ lat P ι ((qOf P : E) ^ m) := hm3 m a3
  simp only [LinearEquiv.coe_coe] at hT hT'
  refine ⟨N + 2 * m, N + 2 * m, fun A B hA hB => ?_⟩
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le hA
  obtain ⟨B, rfl⟩ := Nat.exists_eq_add_of_le hB
  set A' := N + 2 * m + A with hA'
  set B' := N + 2 * m + B with hB'
  let L : AddSubgroup (ι → E) := lat P ι ((qOf P : E) ^ B')⁻¹
  let L' : AddSubgroup (ι → E) := L.comap T.symm.toLinearMap.toAddMonoidHom
  have mL' : ∀ u, u ∈ L' ↔ T.symm u ∈ L := fun u => Iff.rfl
  have hL'le : L' ≤ lat P ι ((qOf P : E) ^ m * ((qOf P : E) ^ B')⁻¹) := fun u hu => by
    have := hT _ _ ((mL' u).1 hu)
    rwa [LinearEquiv.apply_symm_apply] at this
  have hleL' : lat P ι ((qOf P : E) ^ (B' + m))⁻¹ ≤ L' := fun u hu => by
    have := hT' _ _ hu
    rw [mL']
    convert this using 2
    field_simp
    ring
  have hLN : L ≤ lat P ι ((qOf P : E) ^ N)⁻¹ := lat_le (2 * m + B) (by rw [hB']; field_simp; ring)
  have hL'N : L' ≤ lat P ι ((qOf P : E) ^ N)⁻¹ := hL'le.trans (lat_le (m + B) (by rw [hB']; field_simp; ring))
  have hN0 : lat P ι ((qOf P : E) ^ N)⁻¹ ≤ lat P ι ((qOf P : E) ^ 0) := lat_le N (by field_simp)
  have hinj : Function.Injective fun t => T t + b := fun s t h => T.injective (add_right_cancel h)
  have key := h2 (ι → E) K f L L' (Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A' B')
    ((Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A' B').image fun t => T t + b)
    (relIndex_ne_zero_of_cover _ _ _ fun k hk => by
      obtain ⟨s, hs, e⟩ := cov 0 (B' + m) k (hN0 (hLN hk))
      exact ⟨s, hs, hleL' e⟩)
    (relIndex_ne_zero_of_cover _ _ _ fun k hk => cov 0 B' k (hN0 (hL'N hk)))
    (fun v u hu => inv v u (hLN hu)) (fun v u hu => inv v u (hL'N hu)) (sep A' B')
    (fun v hv => cov A' B' v (lat_le (c := (qOf P : E) ^ N) (2 * m + A) (by rw [hA']; ring) (hf.1 v hv)))
    (fun s hs s' hs' h => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hs'
      rw [mL', add_sub_add_right_eq_sub, ← map_sub, LinearEquiv.symm_apply_apply] at h
      rw [sep A' B' t ht t' ht' h])
    (fun v hv => by
      have e1 : v - b ∈ lat P ι ((qOf P : E) ^ (N + m)) :=
        sub_mem (lat_le (c := (qOf P : E) ^ N) m (by ring) (hf.1 v hv)) (lat_le N (by ring) hb)
      obtain ⟨s, hs, e⟩ := cov A' B' _ (lat_le A (by rw [hA']; ring) (hT' _ _ e1))
      refine ⟨T s + b, Finset.mem_image_of_mem _ hs, ?_⟩
      rw [mL']
      convert e using 1
      rw [show v - (T s + b) = (v - b) - T s by abel, map_sub, LinearEquiv.symm_apply_apply])
  rw [Finset.sum_image hinj.injOn] at key
  have hqK : (qOf P : K) ≠ 0 := by
    have : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  have hw : (((qOf P : K) ^ B')⁻¹) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hqK))
  unfold boxSum
  rw [mul_ne_zero_iff_left hw, mul_ne_zero_iff_left hw]
  exact key.symm

end GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFrameCm
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SelfDualFrame

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing
open GlobalTheory.SelfDualGenus

def sw (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E) ≃+* LocAlg v :=
  (Algebra.TensorProduct.comm (maximalRealSubfield E) E
    (v.adicCompletion (maximalRealSubfield E))).toRingEquiv

variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

theorem mem_intV_iff (z : E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    z ∈ intV E v ↔ sw v z ∈ locOrder v := by
  constructor
  · intro hz
    refine (Subring.closure_le
      (t := (locOrder v).toSubring.comap (sw v).toRingHom)).2 ?_ hz
    rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨a, rfl⟩)
    · exact locEmb_mem_locOrder v x
    · exact (locOrder v).algebraMap_mem ⟨a.1, a.2⟩
  · intro hz
    have key : ∀ y ∈ locOrder v, (sw v).symm y ∈ intV E v := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        exact Subring.subset_closure (Or.inl ⟨⟨a, a, rfl⟩, rfl⟩)
      | algebraMap r => exact Subring.subset_closure (Or.inr ⟨⟨r.1, r.2⟩, rfl⟩)
      | add x y _ _ hx hy =>
        rw [map_add (sw v).symm]
        exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    simpa using key _ hz

theorem mem_latS_iff {r : ℕ} (N : Submodule (𝓞 E) (Fin r → E))
    (x : Fin r → E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    x ∈ latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) (intV E v) N ↔
      (fun i => sw v (x i)) ∈ locLattice v N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp only [Pi.zero_apply, map_zero]; exact (locLattice v N).zero_mem
    | add x y _ _ hx hy =>
      have := add_mem hx hy
      convert this using 1
      funext i
      exact map_add (sw v) (x i) (y i)
    | smul c x _ hx =>
      have := smul_mem_locLattice v ((mem_intV_iff v _).1 c.2) hx
      convert this using 1
      funext i
      exact map_mul (sw v) _ _
  · intro hx
    have key : ∀ y ∈ locLattice v N, (fun i => (sw v).symm (y i)) ∈
        latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))
          (intV E v) N := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have := add_mem hx hy
        convert this using 1
        funext i
        exact map_add (sw v).symm (x i) (y i)
      | smul c x _ hx =>
        have hc : (sw v).symm (algebraMap _ (LocAlg v) c) ∈ intV E v :=
          (mem_intV_iff v _).2 (by simpa using (locOrder v).algebraMap_mem c)
        have := Submodule.smul_mem _ (⟨_, hc⟩ : intV E v) hx
        convert this using 1
        funext i
        rw [Pi.smul_apply, Algebra.smul_def]
        exact map_mul (sw v).symm _ _
    simpa using key _ hx

theorem sw_sigR (hc : CMData (maximalRealSubfield E) E)
    (z : E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    sw v (Formalism.UG.sigR hc.sig (v.adicCompletion (maximalRealSubfield E)) z) = locConj v (sw v z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e => rfl

theorem unramified (hc : CMData (maximalRealSubfield E) E) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  Formalism.L2.Pj.unramBridge_holds E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem exists_frame_cm (hc : CMData (maximalRealSubfield E) E) {r : ℕ}
    (J : Matrix (Fin r) (Fin r) E) (hJ : IsHerm (hc.sig : E →+* E) J) (hd : IsUnit J.det)
    (N : Submodule (𝓞 E) (Fin r → E))
    (hN : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex.IsSelfDualLat (hc.sig : E →+* E) J N) :
    ∃ b : GL (Fin r) (E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)),
      cT (Formalism.UG.sigR hc.sig (v.adicCompletion (maximalRealSubfield E))) b.1 *
        J.map (inclE (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))) *
          b.1 = 1 ∧
      ∀ x, x ∈ latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))
        (intV E v) N ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ intV E v := by
  have := unramified hc
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (Jᵀ a b) = Jᵀ b a :=
    fun a b => congrFun (congrFun hJ a) b
  have hd' : Jᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact hd.ne_zero
  have hh : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y = hform (hc.sig : E →+* E) J y x := by
    intro x y
    unfold ReciprocityTheory.ChartRestriction.G.FD.herm hform
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change x j * J i j * ReciprocityTheory.ChartRestriction.G.FD.cc (y i) = ReciprocityTheory.ChartRestriction.G.FD.cc (y i) * J i j * x j
    ring
  have hint : ∀ a : E, a ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ a := by
    intro a
    constructor
    · rintro ⟨b, rfl⟩; exact b.isIntegral_coe
    · intro h; exact ⟨⟨a, h⟩, rfl⟩
  have hsd : ∀ x, x ∈ N ↔ ∀ y ∈ N, IsIntegral ℤ (ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y) := by
    intro x
    have : x ∈ dualSet (hc.sig : E →+* E) J N ↔ x ∈ N := by rw [hN.2.2]; rfl
    rw [← this]
    simp only [hh, ← hint]
    rfl
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame hG hd'
    ⟨Module.Finite.iff_fg.1 hN.1, hN.2.1⟩ hsd v
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    Matrix.transpose_one] at h3
  have hb : ∀ g : GL (Fin r) (LocAlg v), (bc (sw v).symm.toRingHom g).1.map (sw v) = g.1 := by
    intro g
    ext i j
    exact (sw v).apply_symm_apply _
  refine ⟨bc (sw v).symm.toRingHom h, ?_, fun x => ?_⟩
  · apply Matrix.map_injective (f := (sw v).toRingHom) (sw v).injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← h3]
    congr 1
    · congr 1
      ext i j
      exact (sw_sigR v hc _).trans (congrArg (locConj v) ((sw v).apply_symm_apply _))
    · exact hb h
  · rw [mem_latS_iff, h2, ← map_inv]
    refine forall_congr' fun i => ?_
    rw [mem_intV_iff, ← hb h⁻¹]
    have := RingHom.map_mulVec (sw v).toRingHom (bc (sw v).symm.toRingHom h⁻¹).1 x i
    exact Iff.of_eq (congrArg (· ∈ locOrder v) this.symm)

end CM

theorem exists_frame : ∀ (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E))
    (v : HeightOneSpectrum (𝓞 D.host.F)),
    letI := D.host.cmStar
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex.IsSelfDualLat
      (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N →
    ∃ b : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F),
      cT (Formalism.UG.sigR D.sp.cm.sig (v.adicCompletion D.host.F)) b.1 *
        D.sp.gram0.map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) * b.1 = 1 ∧
      ∀ x, x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) N ↔
        ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ intV D.host.E v := by
  intro D N v hN
  letI := D.host.cmStar
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  exact exists_frame_cm v D.sp.cm D.sp.gram0 D.sp.baseGram_isHermitian
    (GlobalTheory.OverCompare.gram_matrix_det_unit D.sp) N hN

end GlobalTheory.SelfDualFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNormalFormLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.QNormalShape

section Abstract

variable {O F : Type} [CommRing O] [Field F] [Algebra O F]

theorem mem_span_basis_iff [IsDomain O] [IsFractionRing O F] {N : ℕ} (b : Module.Basis (Fin N) F (Fin N → F)) (v : Fin N → F) :
    v ∈ Submodule.span O (Set.range b) ↔ ∀ l, b.repr v l ∈ Set.range (algebraMap O F) :=
  b.mem_span_iff_repr_mem O v

theorem isLattice_span_basis {N : ℕ} (b : Module.Basis (Fin N) F (Fin N → F)) :
    Submodule.IsFullLattice F (Submodule.span O (Set.range b)) := by
  have hfg : (Submodule.span O (Set.range b)).FG := Submodule.fg_span (Set.finite_range _)
  have hspan : Submodule.span F (↑(Submodule.span O (Set.range b)) : Set (Fin N → F)) = ⊤ := by
    rw [Submodule.span_span_of_tower, b.span_eq]
  refine { fg := hfg, span_eq_top := hspan, linearIndepOn := ?_ }
  intro s hs hli
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact linearIndepOn_empty F id
  · have : Nontrivial O := (algebraMap O F).domain_nontrivial
    have : FaithfulSMul O F := (faithfulSMul_iff_algebraMap_injective O F).2 <| by
      intro a a' heq
      apply hli.linearIndependent.smul_left_injective ⟨x, hx⟩
      simpa only [id_eq, algebraMap_smul] using congrArg (fun t : F => t • x) heq
    refine Submodule.linearIndepOn_of_finrank_le_finrank_span _ hfg ?_ hs hli
    rw [hspan, finrank_top, Module.finrank_eq_card_basis b]
    exact finrank_range_le_card b

theorem mem_normalForm_iff {Y : Type} [AddCommGroup Y] [Module F Y] [Module O Y] {c : ℕ} (q : O)
    (M : Submodule O Y) (a : Fin c → Y) (e : Fin c → ℤ) (z y : Y) :
    y ∈ IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.normalForm F q M a e z ↔ ∃ m ∈ M, ∃ s : Fin c → O,
      y = m + ∑ i, s i • ((algebraMap O F q) ^ (e i) • (a i + if i.1 = 0 then z else 0)) := by
  unfold IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.normalForm
  rw [← Submodule.span_range_eq_iSup, Submodule.mem_sup]
  simp only [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨m, hm, _, ⟨s, rfl⟩, rfl⟩
    exact ⟨m, hm, s, rfl⟩
  · rintro ⟨m, hm, s, rfl⟩
    exact ⟨m, hm, _, ⟨s, rfl⟩, rfl⟩

theorem irreducible_of_notMem_sq [IsDomain O] [IsDiscreteValuationRing O] {q : O}
    (h1 : q ∈ IsLocalRing.maximalIdeal O) (h2 : q ∉ IsLocalRing.maximalIdeal O ^ 2) : Irreducible q := by
  refine ⟨h1, fun a b hab => ?_⟩
  by_contra h
  rw [not_or] at h
  exact h2 (hab ▸ pow_two (IsLocalRing.maximalIdeal O) ▸ Ideal.mul_mem_mul h.1 h.2)

end Abstract

theorem exists_shape : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalFormCoord → ∀ (E : Type) [Field E] [NumberField E] [StarRing E]
    (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (n c : ℕ)
    (h : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ∃ r ∈ Loc.R1 E n c, ∃ (e : Fin c → ℤ) (z : Fin n → E),
      (r * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z := by
  intro H E _ _ _ P hd n c h
  have hP := P.isPrime
  have hS : P.asIdeal.primeCompl ≤ (𝓞 E)⁰ := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra.ofField E P.asIdeal.primeCompl hS
  have : IsLocalization.AtPrime A P.asIdeal := Localization.subalgebra.isLocalization_ofField E _ hS
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot A
  have : IsFractionRing A E := Localization.subalgebra.isFractionRing_ofField E _ hS
  have hA : ∀ a : E, a ∈ Set.range (algebraMap A E) ↔ IntAt P a := by
    intro a
    constructor
    · rintro ⟨⟨x, r, s, hs, rfl⟩, rfl⟩
      refine ⟨r, s, hs, ?_⟩
      have : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
      change algebraMap (𝓞 E) E s * (algebraMap (𝓞 E) E r * (algebraMap (𝓞 E) E s)⁻¹) = _
      field_simp
    · rintro ⟨r, s, hs, e⟩
      have : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
      refine ⟨⟨a, r, s, hs, ?_⟩, rfl⟩
      rw [← e]
      field_simp
  have hmax : Ideal.map (algebraMap (𝓞 E) A) P.asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P.asIdeal A
  have hq : Irreducible (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E)) := by
    refine irreducible_of_notMem_sq ?_ ?_
    · rw [← hmax]
      exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem _)
    · rw [← hmax, ← Ideal.map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff P.asIdeal.primeCompl]
      rintro ⟨s, hs, hm⟩
      exact (Ideal.IsPrime.mul_mem_pow _ hm).elim hs hd.2
  obtain ⟨r, hr, e, z, hz⟩ := H A E _ hq n c
    (Submodule.span A (Set.range (Pi.basisFun E (Fin n))))
    (by first | exact isLattice_span_basis (Pi.basisFun E (Fin n))
              | exact (isLattice_span_basis (Pi.basisFun E (Fin n))).toIsLattice)
    (Submodule.span A (Set.range ((Pi.basisFun E (Fin (n + c))).map h)))
    (by first | exact isLattice_span_basis ((Pi.basisFun E (Fin (n + c))).map h)
              | exact (isLattice_span_basis ((Pi.basisFun E (Fin (n + c))).map h)).toIsLattice)
  refine ⟨r, hr, e, z, ?_⟩
  have hqE : algebraMap A E (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E)) = (qOf P : E) := by
    rw [map_natCast, map_natCast]
  ext y
  have hy := SetLike.ext_iff.1 hz y
  rw [mem_normalForm_iff, hqE] at hy
  simp only [IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.moveBy, Submodule.mem_map, mem_span_basis_iff, hA, Module.Basis.map_repr,
    LinearEquiv.trans_apply, Pi.basisFun_repr, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe] at hy
  simp only [Set.mem_image, Set.mem_ofPred_eq, IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat, mem_stdAt_iff, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨_, ⟨l, hl, rfl⟩, s, hs⟩ := hy.1 ⟨h v, by simpa [IntV] using hv, rfl⟩
    exact ⟨l, hl, fun i => algebraMap A E (s i), fun i => (hA _).1 ⟨_, rfl⟩, by simpa only [algebraMap_smul] using hs⟩
  · rintro ⟨l, hl, s, hs, rfl⟩
    choose t ht using fun i => (hA _).2 (hs i)
    obtain ⟨v, hv, hv'⟩ := hy.2 ⟨_, ⟨l, hl, rfl⟩, t, by simp only [← ht, algebraMap_smul]⟩
    refine ⟨h.symm v, hv, ?_⟩
    rw [← hv']
    simp

end GlobalTheory.QNormalShape
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsFurther
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.ZerosNearOne

theorem main : ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ D : D7, adm6 D C1 c := by
  obtain ⟨C, c, hC, hc, H⟩ := density_and_regions
  exact ⟨C, c, hC, hc, fun _ => H⟩

end GlobalTheory.ZerosNearOne
end

