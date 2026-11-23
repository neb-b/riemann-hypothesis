module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSobolevInequalityAdelicUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorAutomorphicDerivatives
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1047
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigBasisApply
section
namespace GlobalTheory.ScalarSigmaBasis

open GlobalTheory.UnitLemma

variable {K : UQ} (B : InvAlg K)

theorem sig_smul (r : K.E) (x : B.A) : B.σ (r • x) = K.c r • B.σ x := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]

theorem sig_sum {ι : Type} (s : Finset ι) (f : ι → K.E) (v : ι → B.A) :
    B.σ (∑ i ∈ s, f i • v i) = ∑ i ∈ s, K.c (f i) • B.σ (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]; simp only [sig_smul]

noncomputable def sigBasis {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) : Module.Basis (Fin n) K.E B.A :=
  Module.Basis.mk (v := fun i => B.σ (b i))
    (by
      rw [Fintype.linearIndependent_iff]
      intro f hf i
      have h1 : B.σ (∑ k, f k • B.σ (b k)) = 0 := by rw [hf, map_zero]
      rw [sig_sum] at h1
      simp only [B.σ_σ] at h1
      have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
      have : K.c (f i) = K.c 0 := by rw [h2, map_zero]
      exact K.c.injective this)
    (by
      intro x _
      have h := sig_sum B Finset.univ (fun k => b.repr (B.σ x) k) (fun k => b k)
      have hx : x = ∑ k, K.c (b.repr (B.σ x) k) • B.σ (b k) := by
        rw [← h, b.sum_repr, B.σ_σ]
      rw [hx]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem sigBasis_apply {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) (i : Fin n) :
    sigBasis B b i = B.σ (b i) := by
  simp [sigBasis]

theorem sigBasis_repr {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) (z : B.A) (k : Fin n) :
    (sigBasis B b).repr (B.σ z) k = K.c (b.repr z k) := by
  have hz : B.σ z = ∑ i, K.c (b.repr z i) • sigBasis B b i := by
    conv_lhs => rw [← b.sum_repr z]
    rw [sig_sum]
    simp only [sigBasis_apply]
  rw [hz, Module.Basis.repr_sum_self]

theorem trace_sig (y : B.A) : Algebra.trace K.E B.A (B.σ y) = K.c (Algebra.trace K.E B.A y) := by
  let b := Module.finBasis K.E B.A
  rw [Algebra.trace_eq_matrix_trace (sigBasis B b), Algebra.trace_eq_matrix_trace b]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sigBasis_apply, ← map_mul, sigBasis_repr]

theorem core (a : ℕ) (β : B.A) (hβ : B.σ β = β * ((-1 : B.A) ^ (a - 1) * B.g))
    (b : Module.Basis (Fin a) K.E B.A) (i j : Fin a) :
    K.c (B.herm β (b i) (b j)) = (-1 : K.E) ^ (a - 1) *
      ∑ k, B.herm β (b k) (b i) * LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g) k j := by
  have hg : B.g * b j = ∑ k, b.repr (B.g * b j) k • b k := (b.sum_repr _).symm
  have e1 : B.σ (β * b i * B.σ (b j)) =
      algebraMap K.E B.A ((-1 : K.E) ^ (a - 1)) * (β * (B.g * b j) * B.σ (b i)) := by
    rw [map_mul, map_mul, B.σ_σ, hβ]
    simp only [map_pow, map_neg, map_one]
    ring
  have e2 : β * (B.g * b j) * B.σ (b i) = ∑ k, b.repr (B.g * b j) k • (β * b k * B.σ (b i)) := by
    conv_lhs => rw [hg]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [InvAlg.herm, ← trace_sig, e1, e2, ← Algebra.smul_def, LinearMap.map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smul, smul_eq_mul, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, mul_comm]
  rfl

theorem main : ∀ {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [inst : Field L] (e : GlobalTheory.UnitLemma.UQ.E K ≃+* L) (c : L →+* L), (∀ (x : GlobalTheory.UnitLemma.UQ.E K), (e : GlobalTheory.UnitLemma.UQ.E K → L) ((GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) x) = (c : L → L) ((e : GlobalTheory.UnitLemma.UQ.E K → L) x)) → ∀ (a : ℕ) (β : GlobalTheory.UnitLemma.InvAlg.A B), (GlobalTheory.UnitLemma.InvAlg.σ B : GlobalTheory.UnitLemma.InvAlg.A B → GlobalTheory.UnitLemma.InvAlg.A B) β = β * ((-1 : GlobalTheory.UnitLemma.InvAlg.A B) ^ (a - (1 : ℕ)) * GlobalTheory.UnitLemma.InvAlg.g B) → ∀ (b : Module.Basis (Fin a) (GlobalTheory.UnitLemma.UQ.E K) (GlobalTheory.UnitLemma.InvAlg.A B)), Matrix.map (Matrix.map ((Matrix.of : (Fin a → Fin a → GlobalTheory.UnitLemma.UQ.E K) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) fun (i j : Fin a) ↦ GlobalTheory.UnitLemma.InvAlg.herm B β ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) i) ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) j)) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) (⇑c : L → L) = (-1 : L) ^ (a - (1 : ℕ)) • (Matrix.transpose (Matrix.map ((Matrix.of : (Fin a → Fin a → GlobalTheory.UnitLemma.UQ.E K) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) fun (i j : Fin a) ↦ GlobalTheory.UnitLemma.InvAlg.herm B β ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) i) ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) j)) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) * Matrix.map ((LinearMap.toMatrix b b : (GlobalTheory.UnitLemma.InvAlg.A B →ₗ[GlobalTheory.UnitLemma.UQ.E K] GlobalTheory.UnitLemma.InvAlg.A B) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) (LinearMap.mulLeft (GlobalTheory.UnitLemma.UQ.E K) (GlobalTheory.UnitLemma.InvAlg.g B))) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) := by
  intro K B L _ e c hc a β hβ b
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul]
  rw [← hc, core B a β hβ b i j]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_sum, map_pow, map_neg, map_one]

end GlobalTheory.ScalarSigmaBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemLatGHat
section
namespace GlobalTheory.AdMark

open scoped Matrix

theorem exists_lift {R S La U A : Type} [CommRing R] [CommRing S] [AddCommGroup La] [Module R La] [Module.Projective R La]
    [AddCommGroup U] [Module R U] [AddCommGroup A] [Module S A] (φ : R → S) (fv : U →+ A)
    (hfv : ∀ c x, fv (c • x) = φ c • fv x) (K : A →ₗ[S] A) (hKi : Function.Injective K) (H₁ Hk : AddSubgroup A)
    (hsm : ∀ c, ∀ z ∈ Hk, φ c • z ∈ Hk) (L : Submodule R U) (ι : La →ₗ[R] U) (hι : Function.Injective ι) (N : ℕ)
    (hL : ∀ v, v ∈ L ↔ fv v ∈ Hk) (hK : ∀ z, z ∈ Hk ↔ ∃ y ∈ H₁, K y = z)
    (h1 : ∀ v, fv v ∈ H₁ ↔ ∃ a, ι a = v)
    (ap1 : ∀ y ∈ H₁, ∃ a, ∃ w ∈ H₁, y = fv (ι a) + N • w)
    (apk : ∀ z ∈ Hk, ∃ x ∈ L, ∃ w ∈ Hk, z = fv x + N • w)
    (hdiv : ∀ x z, fv x = N • z → ∃ w, fv w = z ∧ x = N • w) :
    ∃ mk : La →ₗ[R] U, (∀ a, mk a ∈ L) ∧ (∀ a, ∃ w ∈ Hk, fv (mk a) - K (fv (ι a)) = N • w) ∧
      (∀ a, (∃ u ∈ L, mk a = N • u) → ∃ b, a = N • b) ∧ ∀ v ∈ L, ∃ a, ∃ u ∈ L, v = mk a + N • u := by
  let P : Submodule R (U × La) :=
    { carrier := {p | p.1 ∈ L ∧ ∃ w ∈ Hk, fv p.1 - K (fv (ι p.2)) = N • w}
      zero_mem' := ⟨L.zero_mem, 0, zero_mem _, by simp⟩
      add_mem' := by
        rintro p q ⟨hp, w, hw, e⟩ ⟨hq, w', hw', e'⟩
        refine ⟨L.add_mem hp hq, w + w', add_mem hw hw', ?_⟩
        rw [smul_add, ← e, ← e']
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]
        abel
      smul_mem' := by
        rintro c p ⟨hp, w, hw, e⟩
        refine ⟨L.smul_mem c hp, φ c • w, hsm c w hw, ?_⟩
        rw [smul_comm N, ← e]
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, hfv, smul_sub] }
  have hs : Function.Surjective ((LinearMap.snd R U La) ∘ₗ P.subtype) := by
    intro a
    obtain ⟨x, hx, w, hw, e⟩ := apk _ ((hK _).2 ⟨_, (h1 _).2 ⟨a, rfl⟩, rfl⟩)
    exact ⟨⟨(x, a), hx, -w, neg_mem hw, by rw [e]; simp⟩, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hs
  have hs2 : ∀ a, (s a).1.2 = a := fun a => LinearMap.congr_fun hs a
  let mk : La →ₗ[R] U := (LinearMap.fst R U La) ∘ₗ P.subtype ∘ₗ s
  have m1 : ∀ a, mk a ∈ L := fun a => (s a).2.1
  have m2 : ∀ a, ∃ w ∈ Hk, fv (mk a) - K (fv (ι a)) = N • w := fun a => by
    obtain ⟨w, hw, e⟩ := (s a).2.2
    rw [hs2] at e
    exact ⟨w, hw, e⟩
  refine ⟨mk, m1, m2, ?_, ?_⟩
  · rintro a ⟨u, hu, e⟩
    obtain ⟨w, hw, e'⟩ := m2 a
    obtain ⟨y, hy, ey⟩ := (hK _).1 (sub_mem ((hL u).1 hu) hw)
    have : fv (ι a) = N • y := by
      apply hKi
      rw [map_nsmul, ey, smul_sub, ← e', e, map_nsmul]
      abel
    obtain ⟨x, rfl, ex⟩ := hdiv _ _ this
    obtain ⟨b, rfl⟩ := (h1 _).1 hy
    exact ⟨b, hι (by rw [ex, map_nsmul])⟩
  · intro v hv
    obtain ⟨y, hy, ey⟩ := (hK _).1 ((hL v).1 hv)
    obtain ⟨a, w, hw, rfl⟩ := ap1 y hy
    obtain ⟨w', hw', e'⟩ := m2 a
    obtain ⟨u, hu, eu⟩ := hdiv (v - mk a) (K w - w') (by
      rw [map_sub, ← ey, smul_sub, ← e', map_add (f := _), map_nsmul]
      abel)
    refine ⟨a, u, (hL u).2 (hu ▸ sub_mem ((hK _).2 ⟨w, hw, rfl⟩) hw'), ?_⟩
    rw [← eu]
    abel

theorem sub_congr {A : Type} [AddCommGroup A] {x y z w w' : A} {M N c : ℕ} (hc : N = M * c) (e : y - z = M • w)
    (e' : x - z = N • w') : x - y = M • (c • w' - w) := by
  rw [smul_sub, ← mul_smul, ← hc, ← e, ← e']
  abel

end GlobalTheory.AdMark

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdMark

theorem latR_rfl {E : Type} [Field E] [NumberField E] {m : ℕ} (L : Submodule (𝓞 E) (Fin m → E)) :
    latR rfl L = L := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem smul_mem_latGHat {D : D7} (W : HSp D) (k : GA D W) (c : 𝓞 D.host.E) :
    ∀ z ∈ latGHat W k, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z ∈ latGHat W k := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨c • a, (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha, z, hz, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, ← _root_.mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_marking : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Geo.Tor.Level H) (W : HSp D) (r : ℕ) (hr : W.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → l.M ∣ l₂.M → l₂.Mb ≤ l.Mb → ∀ k : GA D W, ∃ mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), IsMark l₂ (latR hr (latG W k)) mk₂ ∧ MarkAd l₂ W hr ι k mk₂ ∧ ∀ mk, (∀ a, mk a ∈ latR hr (latG W k)) → MarkAd l W hr ι k mk → MarkOver l l₂ (latR hr (latG W k)) mk mk₂ := by
  intro D H Dw l l₂ W r hr ι hι hM hMb k
  subst hr
  rw [latR_rfl]
  haveI := Dw.proj
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hM2 : l₂.M ≠ 0 := by have := l₂.three_le; omega
  let fv : (Fin W.rank → D.host.E) →+ (Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (finVec W) (GlobalTheory.AdLat.cap_fv_add D.host.F)
  have ap : ∀ g : GA D W, ∀ z ∈ latGHat W g, ∃ x ∈ latG W g, ∃ w ∈ latGHat W g, z = fv x + l₂.M • w := by
    intro g
    obtain ⟨a1, a2, -, -, a5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D W g
    rw [a5]
    exact (GlobalTheory.AdLat.hat_rational_points_and_approx _ _ _ _ a1 a2).2.1 l₂.M (Nat.pos_of_ne_zero hM2)
  obtain ⟨mk₂, m1, m2, m3, m4⟩ := exists_lift (fun c : 𝓞 D.host.E => (1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) fv
    (fun c x => by
      funext i
      change (1 : Af D.host.F) ⊗ₜ[D.host.F] ((c : D.host.E) * x i) = _ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one])
    (finHom W k).1.mulVecLin
    (fun x y h => by
      have := congrArg (fun v => ((finHom W k)⁻¹).1 *ᵥ v) h
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using this)
    (latGHat W 1) (latGHat W k) (smul_mem_latGHat W k) (latG W k) ι hι.1 l₂.M
    (GlobalTheory.MarkCoset.latG_spec D W k).1 (GlobalTheory.MarkCoset.latG_spec D W k).2
    (fun v => ((GlobalTheory.MarkCoset.latG_spec D W 1).1 v).symm.trans (by rw [← hι.2]; rfl))
    (fun y hy => by
      obtain ⟨x, hx, h⟩ := ap 1 y hy
      rw [← hι.2] at hx
      obtain ⟨a, rfl⟩ := hx
      exact ⟨a, h⟩)
    (ap k) (GlobalTheory.MarkCoset.finVec_div W l₂.M hM2)
  refine ⟨mk₂, ⟨m1, fun a _ => m3 a, fun v hv => ?_⟩, fun a _ => m2 a, fun mk _ hmk a ha => ?_⟩
  · refine Submodule.smul_induction_on hv (fun m hm v hv => ?_) (fun x y hx hy => ?_)
    · obtain ⟨a, u, hu, rfl⟩ := m4 v hv
      refine ⟨m • a, Submodule.smul_mem_smul hm trivial, m • u, Submodule.smul_mem _ m hu, ?_⟩
      rw [smul_add, map_smul, smul_comm m]
    · obtain ⟨a, ha, u, hu, rfl⟩ := hx
      obtain ⟨a', ha', u', hu', rfl⟩ := hy
      exact ⟨a + a', add_mem ha ha', u + u', add_mem hu hu', by rw [map_add (f := _), smul_add]; abel⟩
  · obtain ⟨c, hc⟩ := hM
    obtain ⟨w, hw, e⟩ := hmk a (Submodule.smul_mono_left (Ideal.map_mono hMb) ha)
    obtain ⟨w', hw', e'⟩ := m2 a
    replace e : fv (mk a) - (finHom W k).1.mulVecLin (fv (ι a)) = l.M • w := e
    obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (mk₂ a - mk a) (c • w' - w) (by
      exact (fv.map_sub _ _).trans (sub_congr hc e e'))
    refine ⟨u, ((GlobalTheory.MarkCoset.latG_spec D W k).1 u).2 (hu ▸ sub_mem (nsmul_mem hw' c) hw), ?_⟩
    rw [← eu]
    abel

end GlobalTheory.AdMark
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundForSmoothVectors
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobolevGrowth

theorem lintegral_le_of_count {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {A : Set G} (hA : MeasurableSet A) {h : G → ℝ≥0∞} (hm : Measurable h) (hinv : ∀ γ ∈ Γ, ∀ g, h (γ * g) = h g)
    (M : ℝ) (hM : ∀ y, {γ : G | γ ∈ Γ ∧ γ * y ∈ A}.Finite ∧ (({γ : G | γ ∈ Γ ∧ γ * y ∈ A}.ncard : ℕ) : ℝ) ≤ M) :
    ∫⁻ x in A, h x ∂μ ≤ ENNReal.ofReal M * ∫⁻ x in 𝓕, h x ∂μ := by
  classical
  rw [← lintegral_indicator hA, h𝓕.lintegral_eq_tsum'' (A.indicator h), ← lintegral_tsum, ← lintegral_const_mul _ hm]
  · refine lintegral_mono fun y => ?_
    obtain ⟨hfin, hle⟩ := hM y
    have hfin' : {γ : Γ | (γ : G) * y ∈ A}.Finite := by
      refine Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn
      rintro _ ⟨γ, hγ, rfl⟩
      exact ⟨γ.2, hγ⟩
    have hcard : hfin'.toFinset.card = {γ : G | γ ∈ Γ ∧ γ * y ∈ A}.ncard := by
      rw [← Set.ncard_eq_toFinset_card _ hfin', ← Set.ncard_image_of_injective _ Subtype.val_injective]
      congr 1
      ext g
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨γ.2, hγ⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨g, h1⟩, h2, rfl⟩
    rw [tsum_eq_sum (s := hfin'.toFinset)]
    · have : ∀ γ ∈ hfin'.toFinset, A.indicator h (γ • y) = h y := by
        intro γ hγ
        have h1 : (γ : G) * y ∈ A := by simpa using hγ
        change A.indicator h ((γ : G) * y) = h y
        rw [Set.indicator_of_mem h1, hinv _ γ.2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcard]
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hle
    · intro γ hγ
      have h1 : (γ : G) * y ∉ A := by simpa using hγ
      change A.indicator h ((γ : G) * y) = 0
      exact Set.indicator_of_notMem h1 _
  · intro γ
    exact ((hm.indicator hA).comp (measurable_const_mul (γ : G))).aemeasurable

theorem lintegral_enorm_sq {Q : Type} [MeasurableSpace Q] (ν : Measure Q) (F : Lp ℂ 2 ν) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖F‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := ν) (p := 2) (by norm_num) (Lp.stronglyMeasurable F).aestronglyMeasurable
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F)]
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  exact h.symm

theorem sum_sq_le {α : Type} (S : List α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (S.map fun a => f a ^ 2).sum ≤ (S.map f).sum ^ 2 := by
  induction S with
  | nil => simp
  | cons a S ih =>
    have : 0 ≤ (S.map f).sum := List.sum_nonneg (by simpa using fun a _ => hf a)
    simp only [List.map_cons, List.sum_cons]
    nlinarith [hf a, mul_nonneg (hf a) this]

theorem integral_le_of_count {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Q] (μ : Measure G) [μ.IsMulLeftInvariant]
    (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (π : G → Q) (hmk : Measurable π)
    (hπ : ∀ γ ∈ Γ, ∀ g, π (γ * g) = π g) {Ω : Set G} (hΩ : IsCompact Ω) (z : G) (M : ℝ)
    (hM : ∀ y, {γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o}.ncard : ℕ) : ℝ) ≤ M)
    (F : Lp ℂ 2 ((μ.restrict 𝓕).map π)) (φ : G → ℂ) (hφ : Continuous φ) (hr : ∀ᵐ x ∂μ, F (π x) = φ x) :
    ∫ x in Ω, ‖φ (z * x)‖ ^ 2 ∂μ ≤ M ^ 2 * ‖F‖ ^ 2 := by
  have hFm : Measurable fun x => ‖F x‖ₑ ^ 2 := (Lp.stronglyMeasurable F).measurable.eNorm.pow_const 2
  have hA : IsCompact ((fun o => z * o) '' Ω) := hΩ.image (continuous_const_mul z)
  have key := lintegral_le_of_count μ Γ h𝓕 hA.measurableSet (hFm.comp hmk)
    (fun γ hγ g => by simp only [Function.comp, hπ γ hγ g]) (M ^ 2) (fun y => by
      have e : {γ : G | γ ∈ Γ ∧ γ * y ∈ (fun o => z * o) '' Ω} = {γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o} :=
        Set.ext fun γ => and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ => eq_comm
      rw [e]
      refine ⟨(hM y).1, ?_⟩
      have h1 := (hM y).2
      generalize Set.ncard _ = n at h1
      have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) n
      exact h2.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) h1 2))
  have e1 : ∫⁻ x in 𝓕, ((fun x => ‖F x‖ₑ ^ 2) ∘ π) x ∂μ = ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [← lintegral_enorm_sq]
    exact (lintegral_map hFm hmk).symm
  have e2 : ∫⁻ x in (fun o => z * o) '' Ω, ((fun x => ‖F x‖ₑ ^ 2) ∘ π) x ∂μ =
      ∫⁻ x in Ω, ‖φ (z * x)‖ₑ ^ 2 ∂μ := by
    rw [((measurePreserving_mul_left μ z).setLIntegral_comp_emb (measurableEmbedding_mulLeft z)
      (fun x => ‖φ x‖ₑ ^ 2) Ω)]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hr] with x hx
    simp only [Function.comp, hx]
  rw [e1, e2, ← ENNReal.ofReal_mul (sq_nonneg _)] at key
  have hc : Continuous fun x => ‖φ (z * x)‖ ^ 2 := (hφ.comp (continuous_const_mul z)).norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _) hc.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_of_eq_of_le ?_ key)
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem le_of_sums {α : Type} (S : List α) (I f : α → ℝ) (a C₁ C₂ n : ℝ) (N : ℕ) (hn : 0 ≤ n)
    (hI : ∀ l, 0 ≤ I l) (hf : ∀ l, 0 ≤ f l) (h1 : a ^ 2 ≤ C₁ * (S.map I).sum)
    (h2 : ∀ l ∈ S, I l ≤ (C₂ * n ^ N) ^ 2 * f l ^ 2) : a ≤ √|C₁| * |C₂| * n ^ N * (S.map f).sum := by
  have h2' : (S.map I).sum ≤ (S.map fun l => (C₂ * n ^ N) ^ 2 * f l ^ 2).sum := List.sum_le_sum h2
  rw [List.sum_map_mul_left] at h2'
  have h3 := sum_sq_le S f hf
  have h0 : 0 ≤ (S.map I).sum := List.sum_nonneg (by simpa using fun a _ => hI a)
  have hT : 0 ≤ (S.map f).sum := List.sum_nonneg (by simpa using fun a _ => hf a)
  refine le_of_sq_le_sq ?_ (by positivity)
  have e : (√|C₁| * |C₂| * n ^ N * (S.map f).sum) ^ 2 = |C₁| * ((C₂ * n ^ N) ^ 2 * (S.map f).sum ^ 2) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    ring
  rw [e]
  refine h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) h0).trans ?_)
  exact mul_le_mul_of_nonneg_left (h2'.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))) (abs_nonneg _)

variable {D : D7}

theorem integral_le_adelic (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hp : FinPair V μ 𝓕)
    {Ω : Set (GA D V)} (hΩ : IsCompact Ω) (z : GA D V) (M : ℝ)
    (hM : ∀ y, {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = z * o}.Finite ∧
      (({γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = z * o}.ncard : ℕ) : ℝ) ≤ M)
    (F : Lp ℂ 2 (nuQ V μ 𝓕)) (φ : GA D V → ℂ) (hφ : Continuous φ) (hr : Repr V μ 𝓕 F φ) :
    ∫ x in Ω, ‖φ (z * x)‖ ^ 2 ∂μ ≤ M ^ 2 * ‖F‖ ^ 2 := by
  obtain ⟨-, -, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := hp.haar
  exact integral_le_of_count μ (GQ V) hp.fd (autMk V) measurable_quotient_mk''
    (fun γ hγ g => Quotient.sound (QuotientGroup.rightRel_apply.2 (by
      rw [_root_.mul_inv_rev, mul_inv_cancel_left]
      exact (GQ V).inv_mem hγ))) hΩ z M hM F φ hφ hr

theorem level_of_repr (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    {ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))} (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ)
    {F : Lp ℂ 2 (nuQ V μ 𝓕)} {ψ : GA D V → ℂ} (hψ : Continuous ψ) (hr : Repr V μ 𝓕 F ψ) {k : GA D V} (hk : ρ k F = F)
    (g : GA D V) : ψ (g * k) = ψ g := by
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, huniq, -, htr, -⟩ := _root_.GlobalTheory.HolDict.RepresentativeL2.repr_properties D V μ 𝓕 ρ hp hρ
  have h1 := htr F ψ k hr
  rw [hk] at h1
  exact congrFun (huniq F (rTr V k ψ) ψ (hψ.comp (continuous_mul_const k)) hψ h1 hr) g

theorem normInf_nonneg (θ : InfFam D) (V : HSp D) (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf
  positivity

theorem pointwise_growth : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ (N : ℕ) (S : List (List (D.what₂.Tau × Mt V.rank))), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ ∀ x, ∃ C : ℝ, ∀ F ψ, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → Continuous ψ → Repr V μ 𝓕 F ψ → ∀ u ∈ GinfC V, ‖ψ (x * u)‖ ≤ C * normInf θ V u ^ N * (S.map fun l => ‖l.foldr (dL2 θ V ρ) F‖).sum := by
  intro D θ V hθ μ 𝓕 ρ hp hρ U hU
  obtain ⟨S, Ω, C₁, hS, hΩ, hsob⟩ := _root_.GlobalTheory.SobLoc.local_sobolev D θ V hθ U hU μ hp.haar
  have hcount := _root_.GlobalTheory.RatCount.ncard_rational_le D θ V hθ Ω hΩ
  refine hcount.elim fun N hN => ?_
  refine ⟨N, S, hS, fun x => ?_⟩
  refine (hN x).elim fun C₂ hC₂ => ?_
  refine ⟨√|C₁| * |C₂|, fun F ψ hF hlev hψ hr u hu => ?_⟩
  obtain ⟨ψ', hr', haut, hsm, hder⟩ := _root_.GlobalTheory.SmoothRep.exists_smooth_repr D θ V hθ μ 𝓕 ρ hp hρ U hU F hF hlev
  have e : ψ' = ψ := (_root_.GlobalTheory.HolDict.RepresentativeL2.repr_properties D V μ 𝓕 ρ hp hρ).2.1 F ψ' ψ haut.cont hψ hr' hr
  subst e
  have h1 := hsob ψ' hψ (fun k hk hk' => level_of_repr V hp hρ hψ hr (hlev k hk hk')) (fun l hl => (hder l hl).1) hsm (x * u)
  have h2 := fun l hl => integral_le_adelic V hp hΩ (x * u) _ (hC₂ u hu) _ _ (hder l (hS l hl)).1 (hder l (hS l hl)).2
  have h3 := le_of_sums S
    (fun l => ∫ o in Ω, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ') (x * u * o)‖ ^ 2 ∂μ)
    (fun l => ‖l.foldr (dL2 θ V ρ) F‖) ‖ψ' (x * u)‖ C₁ C₂ (normInf θ V u) N (normInf_nonneg θ V u)
    (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun _ => norm_nonneg _) h1 h2
  exact h3

end GlobalTheory.SobolevGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StExpDeriv
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Pc3

noncomputable def pBLin {n : ℕ} (ε : Fin n → Bool) : (Mode ε → ℂ) →ₗ[ℝ] Mat n where
  toFun := pB ε
  map_add' B C := by
    funext a b
    simp only [pB, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> simp [star_add]
  map_smul' r B := by
    funext a b
    simp only [pB, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul, star_mul', Complex.conj_ofReal]

theorem pB_mode {n : ℕ} (ε : Fin n → Bool) (B : Mode ε → ℂ) (x : Mode ε) :
    pB ε B x.1.1 x.1.2 = B x := by
  unfold pB
  rw [dite_eq_left x.2]

theorem stExpDeriv : StExpDeriv := by
  intro n ε
  obtain ⟨⟨L, hL, hD⟩, h2⟩ :=
    GlobalTheory.exp_conj_entries_hasFDerivAt_zero n (Mode ε) (pBLin ε) (fun x => x.1)
  refine ⟨?_, fun s => ?_⟩
  · have hLid : L = ContinuousLinearMap.id ℝ (Mode ε → ℂ) := by
      ext1 w; funext x
      rw [hL]
      exact pB_mode ε w x
    rw [← hLid]
    exact hD
  · obtain ⟨L', hL', hD'⟩ := h2 (Matrix.diagonal s)
    refine ⟨L', fun w x => ?_, hD'⟩
    rw [hL']
    change (Matrix.diagonal s * pB ε w - pB ε w * Matrix.diagonal s) x.1.1 x.1.2 = _
    rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, pB_mode]
    ring

end GlobalTheory.PsCo.Pc3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjOfTwistedNormConjHermitianTripleRegulStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedConj_of_twistedNormConj_hermitianTriple_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z δ' z' : Gr G r), 0 < r → regular₂ G γ → IsNrm G r γ δ z → IsNrm G r γ δ' z' → ∃ g : Gr G r, δ' = g⁻¹ * δ * sigG G r g ∧ ∀ y ∈ Subgroup.centralizer {γ}, carry G r z' y = g⁻¹ * carry G r z y * g := by
  first | (exact @GlobalTheory.NrmUnique.nrm_unique) | (exact GlobalTheory.NrmUnique.nrm_unique) | (intros; apply GlobalTheory.NrmUnique.nrm_unique <;> assumption)
end

