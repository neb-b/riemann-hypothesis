module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3108
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.EpsMulSub
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FinrankWPow
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.Ord.DimsAlg

variable {k : Type} [Field k] {C : Type} [CommRing C]

private abbrev W (ν : C → k) : Submodule k (k ⊗[ℤ] C) :=
  ⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (ν c)

private theorem mem_W (ν : C → k) (x : k ⊗[ℤ] C) :
    x ∈ W ν ↔ ∀ c : C, ∃ n : ℕ, (((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) ^ n) * x = 0 := by
  simp only [W, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace]
  refine forall_congr' fun c => exists_congr fun n => ?_
  have h : (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c - ν c • (1 : Module.End k (k ⊗[ℤ] C)))
      = Algebra.lmul k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) := by
    have : ν c ⊗ₜ[ℤ] (1 : C) = ν c • (1 : k ⊗[ℤ] C) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [this, map_sub, map_smul, map_one]
    rfl
  rw [h, ← map_pow]
  rfl

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

private def frobZ : k ≃ₐ[ℤ] k := AlgEquiv.ofRingEquiv (f := frobeniusEquiv k p) (fun n => by simp)

private def E : (k ⊗[ℤ] C) ≃ₐ[ℤ] (k ⊗[ℤ] C) := Algebra.TensorProduct.congr (frobZ (k := k) p) AlgEquiv.refl

private theorem E_tmul (l : k) (c : C) : E p (l ⊗ₜ[ℤ] c) = (l ^ p) ⊗ₜ[ℤ] c := by
  simp [E, frobZ, frobenius_def]

private theorem E_smul (l : k) (x : k ⊗[ℤ] C) : E p (l • x) = l ^ p • E p x := by
  induction x with
  | tmul a c => simp [TensorProduct.smul_tmul', E_tmul, mul_pow]
  | add x y hx hy => simp [smul_add, hx, hy]

private theorem E_mem (ν : C → k) (x : k ⊗[ℤ] C) : E p x ∈ W (fun c => ν c ^ p) ↔ x ∈ W ν := by
  rw [mem_W, mem_W]
  refine forall_congr' fun c => exists_congr fun n => ?_
  have h : E p (((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) ^ n * x)
      = ((1 : k) ⊗ₜ[ℤ] c - (ν c ^ p) ⊗ₜ[ℤ] (1 : C)) ^ n * E p x := by
    rw [map_mul, map_pow, map_sub, E_tmul, E_tmul, one_pow]
  rw [← h]
  exact map_eq_zero_iff _ (E p).injective

private theorem finrank_W_pow (ν : C → k) :
    Module.finrank k ↥(W (fun c => ν c ^ p)) = Module.finrank k ↥(W ν) := by
  let j : ↥(W ν) ≃+ ↥(W (fun c => ν c ^ p)) :=
    { toFun := fun x => ⟨E p x.1, (E_mem p ν x.1).2 x.2⟩
      invFun := fun y => ⟨(E p).symm y.1, (E_mem p ν _).1 (by simpa using y.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hr := rank_eq_of_equiv_equiv (R := k) (R' := k) (M := ↥(W ν)) (M₁ := ↥(W (fun c => ν c ^ p)))
    (⟨fun l => l ^ p, by simp [(Fact.out : p.Prime).ne_zero]⟩ : ZeroHom k k) j
    (frobeniusEquiv k p).bijective (fun r m => Subtype.ext (E_smul p r m.1))
  exact (congrArg Cardinal.toNat hr).symm

end UpperTheory.Gal.Ord.DimsAlg

namespace UpperTheory.Gal.Ord.DimsCoh

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {k : Type} [Field k] {t : Sp k ⟶ Sp R}

private def cohHom (o : Obj b N t) : 𝓞 D.F →+* Module.End k (primDR o.A) :=
  RingHom.mk'
    { toFun := coh o
      map_one' := by
        haveI := o.act.hom
        refine LinearMap.ext fun x => ?_
        exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_id _ _ _ (by rw [map_one, o.act.one]) x
      map_mul' := fun x y => by
        haveI := o.act.hom
        refine LinearMap.ext fun c => ?_
        exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_comp _ _ _ _ _ (by rw [mul_comm x y, map_mul, o.act.mul]) c }
    fun x y => by
      haveI := o.act.hom
      refine LinearMap.ext fun c => ?_
      exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_mul _ _ _ _ _ (by rw [map_add (f := _), o.act.add]) c

end UpperTheory.Gal.Ord.DimsCoh

open UpperTheory.Gal.Ord.DimsAlg UpperTheory.Gal.Ord.DimsCoh in
theorem UpperTheory.Gal.Ord.dims :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ j : ℕ, Module.finrank k ↥(⨅ c, (coh o c).maxGenEigenspace (β (b.t i c) ^ p ^ j)) =
        Module.finrank k ↥(⨅ c, (coh o c).maxGenEigenspace (β (b.t i c))) := by
  intro p _ D R _ b N hN hNp _ k _ _ hk β o i w f _ _ _ π j
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o.A o.ab
  obtain ⟨hfd, -, -⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o.A g o.ab hg
  haveI := hfd
  haveI : Module.Finite k (primDR o.A) := (Module.finite_dual_iff k).1 hfd
  haveI := D.freeLa
  haveI := D.finLa
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hk
  obtain ⟨l, hlp, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : l.Coprime p := (Nat.coprime_primes hl (Fact.out : p.Prime)).2 (by omega)
  have hcopj : ∀ j : ℕ, (l ^ j).Coprime p := fun j => Nat.Coprime.pow_left j hcop
  have hposj : ∀ j : ℕ, 0 < l ^ j := fun j => pow_pos hl.pos j
  have hlk : (l : k) ≠ 0 := by
    have hu := (b.unit l hcop).map β
    rw [map_natCast] at hu
    exact hu.ne_zero
  obtain ⟨I, -⟩ := o.geom k (𝟙 _) β (by rw [Category.id_comp])
  have hc : ∀ c : 𝓞 D.F, LinearMap.charpoly (cohHom o c) =
      ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n)).map (Int.castRingHom k) := by
    intro c
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    have e := GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic k o.A o.ab (o.act.act (algebraMap (𝓞 D.F) D.O c)) D.La
      (DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) l hl hlk (fun j => I.ev (l ^ j))
      (fun j x y => I.add (l ^ j) x y) (fun j x => I.lin (l ^ j) _ x)
      (fun j x => I.ker (l ^ j) (hposj j) (hcopj j) x) (fun j q => I.onto (l ^ j) (hposj j) (hcopj j) q)
    rw [GlobalTheory.T.charpoly_la_eq_pow p D c] at e
    rw [← e]
    exact (GlobalTheory.DeRhamCharpolyP.charpoly_dualMap _).symm
  have key := fun χ : 𝓞 D.F →+* k => GlobalTheory.T.finrank_jointWeightSpace_eq_of_charpoly k (𝓞 D.F) ↥(primDR o.A) (cohHom o) (D.m * D.n) hc χ
  have e1 := key ((iterateFrobenius k p j).comp (β.comp (b.t i)))
  have e2 := key (β.comp (b.t i))
  have hW : ∀ (j : ℕ) , Module.finrank k ↥(W (C := 𝓞 D.F) (fun c => β (b.t i c) ^ p ^ j)) =
      Module.finrank k ↥(W (C := 𝓞 D.F) (fun c => β (b.t i c))) := by
    intro j
    induction j with
    | zero => exact congrArg (fun ν : 𝓞 D.F → k => Module.finrank k ↥(W ν)) (funext fun c => by simp)
    | succ j ih =>
      rw [← ih, ← finrank_W_pow p (fun c => β (b.t i c) ^ p ^ j)]
      exact congrArg (fun ν : 𝓞 D.F → k => Module.finrank k ↥(W ν)) (funext fun c => by rw [_root_.pow_succ, _root_.pow_mul])
  simp only [RingHom.comp_apply, iterateFrobenius_def] at e1 e2
  refine e1.trans (Eq.trans ?_ e2.symm)
  exact congrArg (D.m * D.n * ·) (hW j)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.KsCore
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem exists_rep {k H : Type*} [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H]
    (φ : LinearMap.BilinForm k H) (hskew : ∀ x y, φ x y = -φ y x) (hnd : ∀ x, (∀ y, φ x y = 0) → x = 0)
    (L : H →ₗ[k] k) : ∃ α, ∀ h, φ h α = L h := by
  have hinj : Function.Injective φ.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hnd
    intro h
    have this : φ h y = 0 := LinearMap.congr_fun hy h
    rw [hskew, this, neg_zero]
  have hsurj : Function.Surjective φ.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj
  obtain ⟨α, hα⟩ := hsurj L
  exact ⟨α, fun h => by rw [← hα]; rfl⟩

private theorem ks_core {k H C : Type*} [Field k] [AddCommGroup H] [Module k H] [CommRing C]
    (σ : C →+* Module.End k H) (bar : C → C) (χ : C →+* k) (φ : LinearMap.BilinForm k H) (Fl : Submodule k H)
    (hskew : ∀ x y, φ x y = -φ y x) (hnd : ∀ x, (∀ y, φ x y = 0) → x = 0)
    (hiso : ∀ x ∈ Fl, ∀ y ∈ Fl, φ x y = 0)
    (hadj : ∀ c x y, φ (σ c x) y = φ x (σ (bar c) y))
    (ω e : C) (T r : k) (hT : ∀ v, σ ω v + σ (bar ω) v = T • v) (hdisc : 2 * r - T ≠ 0)
    (hL1 : ∀ c h, σ c (σ e h) - χ c • σ e h ∈ Fl) (hL3 : ∀ h, σ ω (σ e h) = r • σ e h)
    (h₀ : H) (hh₀ : σ e h₀ ∉ Fl) (x : H) (hxe : σ e x = x) (α : H)
    (hα : ∀ c h, φ (σ c h) α = χ c * φ h α) (hxα : φ x α ≠ 0) :
    ∃ g : H →ₗ[k] H,
      (∀ c, ∀ u ∈ Fl, g (σ c u) - σ c (g u) ∈ Fl) ∧
      (∀ (n : ℕ) (lam : Fin n → k) (c : Fin n → C) (u : H), ∑ l, lam l * χ (c l) = 0 →
        g (∑ l, lam l • σ (c l) ((σ ω - (T - r) • 1) u)) = 0) ∧
      (∀ u ∈ Fl, ∀ v ∈ Fl, φ (g u) v + φ u (g v) = 0) ∧ g x ∉ Fl := by
  have hcomm : ∀ a b v, σ a (σ b v) = σ b (σ a v) := by
    intro a b v
    show (σ a * σ b) v = (σ b * σ a) v
    rw [← map_mul, ← map_mul, mul_comm]
  have hbar : ∀ v, σ (bar ω) v = T • v - σ ω v := by
    intro v
    rw [← hT v]
    abel
  have hzw : ∀ c, σ ω (σ c (σ e h₀)) = r • σ c (σ e h₀) := by
    intro c
    rw [hcomm, hL3 h₀, map_smul]
  have hαc : ∀ c, σ c α = χ (bar c) • α := by
    intro c
    rw [← sub_eq_zero]
    apply hnd
    intro y
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hadj c α y,
      hskew α (σ (bar c) y), hα (bar c) y, hskew α y]
    ring
  have hwfl : ∀ c, ∀ u ∈ Fl, φ u (σ (bar c) (σ e h₀)) = χ (bar c) * φ u (σ e h₀) := by
    intro c u hu
    have h1 := hiso u hu _ (hL1 (bar c) h₀)
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h1
    exact h1
  have hxw : φ x (σ e h₀) = 0 := by
    have h1 : φ (σ ω x) (σ e h₀) = r * φ x (σ e h₀) := by
      rw [← hxe, hL3 x, hxe, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have h2 : φ (σ ω x) (σ e h₀) = (T - r) * φ x (σ e h₀) := by
      rw [hadj, hbar, hL3 h₀, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    have h3 : (2 * r - T) * φ x (σ e h₀) = 0 := by
      linear_combination h2 - h1
    exact (mul_eq_zero.1 h3).resolve_left hdisc
  have hPz : ∀ d v, φ ((σ ω - (T - r) • 1) v) (σ d (σ e h₀)) = 0 := by
    intro d v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul,
      smul_eq_mul]
    rw [hadj, hbar, hzw, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have happ : ∀ u, ((φ.flip α).smulRight (σ e h₀) + (φ.flip (σ e h₀)).smulRight α) u =
      φ u α • σ e h₀ + φ u (σ e h₀) • α := fun u => rfl
  refine ⟨(φ.flip α).smulRight (σ e h₀) + (φ.flip (σ e h₀)).smulRight α, ?_, ?_, ?_, ?_⟩
  · intro c u hu
    rw [happ, happ, map_add (f := _), map_smul, map_smul, hα c u, hadj c u (σ e h₀), hwfl c u hu, hαc c]
    have key : (χ c * φ u α) • σ e h₀ + (χ (bar c) * φ u (σ e h₀)) • α -
        (φ u α • σ c (σ e h₀) + φ u (σ e h₀) • χ (bar c) • α) =
        -(φ u α • (σ c (σ e h₀) - χ c • σ e h₀)) := by
      module
    rw [key]
    exact Fl.neg_mem (Fl.smul_mem _ (hL1 c h₀))
  · intro n lam c u hsum
    rw [happ]
    have h1 : φ (∑ l, lam l • σ (c l) ((σ ω - (T - r) • 1) u)) α = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hα]
      have e1 : ∀ l, lam l * (χ (c l) * φ ((σ ω - (T - r) • 1) u) α) =
          (lam l * χ (c l)) * φ ((σ ω - (T - r) • 1) u) α := fun l => by ring
      rw [Finset.sum_congr rfl fun l _ => e1 l, ← Finset.sum_mul, hsum, zero_mul]
    have h2 : φ (∑ l, lam l • σ (c l) ((σ ω - (T - r) • 1) u)) (σ e h₀) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hadj, hPz,
        mul_zero, Finset.sum_const_zero]
    rw [h1, h2, zero_smul, zero_smul, add_zero]
  · intro u _ v _
    rw [happ, happ, map_add (f := _), map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hskew (σ e h₀) v, hskew α v]
    ring
  · rw [happ, hxw, zero_smul, add_zero]
    intro hmem
    apply hh₀
    have := Fl.smul_mem (φ x α)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hxα, one_smul] at this

theorem UpperTheory.Gal.Ord.ks :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ φ : LinearMap.BilinForm k (HdR o.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o.A o.A o.P φ → ∀ x ∈ Fil o.A, hom o π.ε x = x →
      (∃ y, (∀ c, coh o c y = β (b.t i c) • y) ∧ x y ≠ 0) →
      ∃ g : HdR o.A →ₗ[k] HdR o.A, GlobalTheory.UPel.Sm.IsKS (GlobalTheory.HTCount.crysAct o) φ (Fil o.A) (GlobalTheory.HTCount.lieZ o β) g ∧ g x ∉ Fil o.A := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i w f hw hf hf0 π φ hφ x hxF hxe hyex
  obtain ⟨y, hy, hxy⟩ := hyex
  obtain ⟨hfd, -, hskew, hiso⟩ := GlobalTheory.T.harrisTaylor_pairing_skew_hodge_lagrangian p D R b N hN hNp k (spMap β) o β rfl φ hφ
  have hnd := _root_.GlobalTheory.HTPolPair.nondeg p D R b N hN hNp k (spMap β) o β rfl φ hφ
  have hadj0 := GlobalTheory.T.harrisTaylor_crystal_action_adjoint p D R b N hN hNp k (spMap β) o β rfl φ hφ
  obtain ⟨hL1, ⟨h₀, hh₀, -⟩, hL3⟩ := lie p D R b N hN hNp hm k hk β o i w f hw hf hf0 π
  haveI := hfd
  let L : HdR o.A →ₗ[k] k :=
    { toFun := fun h => h y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨α, hα0⟩ := exists_rep φ hskew hnd L
  let σ : 𝓞 D.F →+* Module.End k (HdR o.A) := (GlobalTheory.HTCount.crysAct o).comp (algebraMap (𝓞 D.F) D.O)
  have hadj : ∀ c u v, φ (σ c u) v = φ u (σ (D.bar c) v) := by
    intro c u v
    have := hadj0 (algebraMap _ _ c) u v
    rwa [D.star_F, MulOpposite.unop_op] at this
  have hT : ∀ v, σ D.ω v + σ (D.bar D.ω) v = (D.tr : k) • v := by
    intro v
    have e1 : σ D.ω + σ (D.bar D.ω) = σ (D.tr : 𝓞 D.F) := by
      rw [← map_add (f := _), D.tr_eq]
    have e2 := LinearMap.congr_fun e1 v
    rw [LinearMap.add_apply, map_intCast] at e2
    rw [e2]
    simp only [Module.End.intCast_apply]
    exact (Int.cast_smul_eq_zsmul k D.tr v).symm
  have hdisc : 2 * β b.ρ - (D.tr : k) ≠ 0 := by
    haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 hk
    intro h0
    have hr := congrArg β b.ρ_root
    simp only [map_add (f := _), map_sub, map_pow, map_mul, map_intCast, map_zero] at hr
    have e3 : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (2 * β b.ρ - D.tr) * h0 - 4 * hr
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).1 e3)
  have hα : ∀ c h, φ (σ c h) α = (β.comp (b.t i)) c * φ h α := by
    intro c h
    rw [hα0, hα0]
    show h (coh o c y) = _
    rw [hy c, map_smul, smul_eq_mul]
    rfl
  have hxα : φ x α ≠ 0 := by
    rw [hα0]
    exact hxy
  obtain ⟨g, ga, gb, gc, gd⟩ := ks_core σ D.bar (β.comp (b.t i)) φ (Fil o.A) hskew hnd hiso hadj D.ω π.ε
    (D.tr : k) (β b.ρ) hT hdisc hL1 hL3 h₀ hh₀ x hxe α hα hxα
  refine ⟨g, ⟨?_, ?_, gc⟩, gd⟩
  · intro a u hu
    obtain ⟨c, rfl⟩ := surjO p D hm a
    exact ga c u hu
  · intro z hz
    have hle : GlobalTheory.HTCount.lieZ o β ≤ (Fil o.A).comap g := by
      apply Submodule.span_le.2
      rintro z ⟨n, lam, c, y', hy', hsum, rfl⟩
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hy'
      exact (congrArg (· ∈ Fil o.A) (gb n lam c u (hsum i))).mpr (Fil o.A).zero_mem
    exact hle hz
end

