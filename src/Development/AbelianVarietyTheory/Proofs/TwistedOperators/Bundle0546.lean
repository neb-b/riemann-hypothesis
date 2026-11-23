module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0538
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0415

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPai
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweRealSmall

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

private theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

private theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have e := RingHom.map_det τ J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

private theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

private theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

private theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

private theorem actsD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  simp only [e, map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

theorem howe_real_ker' : GlobalTheory.Published.HoweDualityReal →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM
  have hT := hM.triple
  have hg := hT.geo
  have hc := hT.chars
  have hR := hM.real
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have dV' : G.V'.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)
  have dW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have hres := resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk := hecke_div hc.heckeα hc.heckeβ
  obtain ⟨hbdd, hsum⟩ := hHD F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hLie := _root_.GlobalTheory.RealLieFock.lie_deriv_pol F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hCpt := _root_.GlobalTheory.FockCompactW.pol_stable_compact F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  refine ⟨hbdd, ?_⟩
  intro N hN hNe φ hφ
  set K : Submodule ℂ (SInf F (Fin a' × Fin (a + a'))) := LinearMap.ker R.p' ⊓ G.M'.Pol Bs.ψ Bs.emb with hKdef
  have hK : GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' K := by
    refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
    · intro γ hγ f hf f₁ hact
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hR.quot'.lie γ hγ f hf f₁ hact), hN.1 (hN.2.1 γ hγ f hf f₁ hact)⟩
    · intro k hk f hf f₁ hact
      refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, hN.1 (hN.2.2.1 k hk f hf f₁ hact)⟩
      rw [map_sub, hR.quot'.cpt k hk f hf f₁ hact, sub_self]
    · intro γ hγ f hf f₁ hact
      have hf' := Submodule.mem_inf.1 hf
      have hp := hR.lie γ hγ 0 (zero_mem _) f hf'.2 0 f₁
        (actsD_zero (fun t => om (1, γ (Multiplicative.ofAdd t)))) hact
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hf'.1).symm)
      rw [map_zero] at hp
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, (hLie γ hγ f hf'.2).2 f₁ hact⟩
    · intro k hk f hf f₁ hact
      have hf' := Submodule.mem_inf.1 hf
      have hp := hR.cpt k hk 0 (zero_mem _) f hf'.2 0 f₁ (acts_zero _) hact
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hf'.1).symm)
      rw [map_zero] at hp
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, (hCpt k hk f hf'.2).2 f₁ hact⟩
  have hKne : K ≠ G.M'.Pol Bs.ψ Bs.emb := by
    intro hKe
    have hbot : (G.M'.Pol Bs.ψ Bs.emb).map R.p' = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨f, hf, rfl⟩
      rw [← hKe] at hf
      exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hf).1
    rw [hR.quot'.onto] at hbot
    haveI := hR.nontriv
    exact top_ne_bot hbot
  have hNK : N ⊔ K ≠ G.M'.Pol Bs.ψ Bs.emb := hsum N K hN hK hNe hKne
  rcases hR.irred (N.map R.p') (by
    intro γ hγ f hf f₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    obtain ⟨n₁, hactn⟩ := (hLie γ hγ n (hN.1 hn)).1
    rw [hR.lie γ hγ f hf n (hN.1 hn) f₁ n₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem (hN.2.2.2.1 γ hγ n hn n₁ hactn)) (by
    intro k hk f hf f₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    obtain ⟨n₁, hactn⟩ := (hCpt k hk n (hN.1 hn)).1
    rw [hR.cpt k hk f hf n (hN.1 hn) f₁ n₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem (hN.2.2.2.2 k hk n hn n₁ hactn)) with h0 | htop
  · have hmem : R.p' φ ∈ N.map R.p' := Submodule.mem_map_of_mem hφ
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · exfalso
    apply hNK
    refine le_antisymm (sup_le hN.1 inf_le_right) ?_
    intro f hf
    have hm : R.p' f ∈ N.map R.p' := by rw [htop]; exact Submodule.mem_top
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hm
    have hk : f - n ∈ K :=
      Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hpn, sub_self]), sub_mem hf (hN.1 hn)⟩
    have := Submodule.add_mem_sup hn hk
    rwa [add_sub_cancel] at this

end GlobalTheory.HoweRealSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdVLeOfLoc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff Pointwise

noncomputable section

namespace GlobalTheory.StairLine

open GlobalTheory.SeeSaw (FI idV dI)

variable {D : D7}


set_option maxHeartbeats 800000 in
theorem line_mem_iff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FI D) (q : Fin c) (hq : 2 * q.1 + 1 ≠ c)
    {x : D.host.E} (hx : x ≠ 0) (v : GlobalTheory.FinPl.Pl D) (a : AE D) :
    (fun k => a * incA D (x * d.a k q)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔
      a ∈ idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q) v := by
  classical
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσdef
  have hσ : ∀ e, σ (σ e) = e := fun e => star_star e
  have hG : Formalism.UG.cT σ B.gram = B.gram := by funext i j; exact B.herm.eq (B.frame j) (B.frame i)
  have eT : ∀ {m n p : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) (Y : Matrix (Fin n) (Fin p) D.host.E),
      Formalism.UG.cT σ (X * Y) = Formalism.UG.cT σ Y * Formalism.UG.cT σ X := by
    intros; simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have eTT : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), Formalism.UG.cT σ (Formalism.UG.cT σ X) = X := by
    intros; ext i j; simp [Formalism.UG.cT, hσ]
  have hperp : Formalism.UG.cT σ d.a * B.gram * frameMat B A d.ι = 0 := by
    have h1 := congrArg (Formalism.UG.cT σ) d.perp
    rw [eT, eT, eTT, hG, ← Matrix.mul_assoc] at h1
    rw [h1]; ext i j; simp [Formalism.UG.cT]
  let P := Formalism.UG.cT σ d.a * B.gram
  let r : Fin B.rank → D.host.E := x⁻¹ • P q.rev
  have hrow : ∀ {n : ℕ} (N : Matrix (Fin B.rank) (Fin n) D.host.E), r ᵥ* N = x⁻¹ • (P * N) q.rev := by
    intros; funext j; simp [r, Matrix.vecMul, dotProduct, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  have hrM : ∀ y, r ⬝ᵥ (frameMat B A d.ι *ᵥ y) = 0 := by
    intro y
    rw [Matrix.dotProduct_mulVec, hrow, show P * frameMat B A d.ι = 0 from hperp,
      show ((0 : Matrix (Fin c) (Fin A.rank) D.host.E) q.rev) = 0 from rfl, smul_zero, zero_dotProduct]
  have hgram : P * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  have hra : ∀ u : Fin c → D.host.E, r ⬝ᵥ (d.a *ᵥ u) = x⁻¹ * u q := by
    intro u
    rw [Matrix.dotProduct_mulVec, hrow, hgram]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, antiDiagonalSignGramMatrix]
    rw [Finset.sum_eq_single q]
    · have h1 : q.rev.1 + q.1 + 1 = c := by rw [Fin.val_rev]; omega
      have h2 : q.rev ≠ q := by intro h; rw [Fin.ext_iff, Fin.val_rev] at h; omega
      rw [if_pos h1, if_neg h2, mul_one]
    · intro p _ hp
      have : ¬ (q.rev.1 + p.1 + 1 = c) := by
        intro h; apply hp; rw [Fin.ext_iff]; rw [Fin.val_rev] at h; omega
      rw [if_neg this, mul_zero, zero_mul]
    · simp
  have hlat : ∀ y ∈ d.lat Λ 𝔟, r ⬝ᵥ y ∈ FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q := by
    rintro _ ⟨y, -, u, hu, rfl⟩
    rw [dotProduct_add, hrM, zero_add, hra]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) (hu q)
  have hcol : r ⬝ᵥ (fun k => x * d.a k q) = 1 := by
    have e : (fun k => x * d.a k q) = d.a *ᵥ Pi.single q x := by
      funext k; simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    rw [e, hra, Pi.single_eq_same, inv_mul_cancel₀ hx]
  constructor
  · intro hmem
    have hΦ : ∀ Y ∈ latV B (d.lat Λ 𝔟) (· = v), ∑ k, incA D (r k) * Y k ∈
        idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q) v := by
      intro Y hY
      induction hY using AddSubgroup.closure_induction with
      | mem Y hY =>
        obtain ⟨α, h1, h2, b, hb, y, hy, rfl⟩ := hY
        rw [Set.mem_singleton_iff] at hb
        subst hb
        refine AddSubgroup.subset_closure ⟨α, h1, h2, _, hlat y hy, ?_⟩
        simp only [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul, ← TensorProduct.tmul_sum, dotProduct]
      | zero => simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact zero_mem _
      | add Y Z _ _ hY hZ =>
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; exact add_mem hY hZ
      | neg Y _ hY =>
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]; exact neg_mem hY
    have h := hΦ _ hmem
    have e : ∑ k, incA D (r k) * (a * incA D (x * d.a k q)) = a := by
      calc _ = a * incA D (r ⬝ᵥ (fun k => x * d.a k q)) := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [dotProduct, map_sum, map_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
        _ = a := by rw [hcol, map_one, mul_one]
    rwa [e] at h
  · intro ha
    induction ha using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, h1, h2, b, hb, rfl⟩ := hz
      obtain ⟨b', hb', rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hb
      refine AddSubgroup.subset_closure ⟨α, h1, h2, 1, rfl, d.a *ᵥ Pi.single q b', ?_, ?_⟩
      · refine ⟨0, Λ.zero_mem, Pi.single q b', fun p => ?_, by simp⟩
        by_cases hp : p = q
        · subst hp; simpa using hb'
        · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
      · funext k
        have e1 : x * d.a k q * (x⁻¹ * b') = 1 * (d.a *ᵥ Pi.single q b') k := by
          simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
          field_simp
        rw [mul_comm (pairA D.host.F 0 α ⊗ₜ[D.host.F] (x⁻¹ * b')), GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, e1]
    | zero =>
      have e0 : (fun k => (0 : AE D) * incA D (x * d.a k q)) = 0 := by funext k; exact zero_mul _
      rw [e0]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : (fun k => (y + z) * incA D (x * d.a k q)) =
          (fun k => y * incA D (x * d.a k q)) + fun k => z * incA D (x * d.a k q) := by
        funext k; simp [add_mul]
      rw [this]; exact add_mem hy hz
    | neg y _ hy =>
      have : (fun k => -y * incA D (x * d.a k q)) = -fun k => y * incA D (x * d.a k q) := by
        funext k; simp [neg_mul]
      rw [this]; exact neg_mem hy

theorem idV_le_of_loc {𝔞 𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D}
    (h : ∀ z ∈ 𝔞, ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap D.host.F D.host.E t * z ∈ 𝔟) : idV 𝔞 v ≤ idV 𝔟 v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, h1, h2, a, ha, rfl⟩
  obtain ⟨t, ht, htb⟩ := h a ha
  obtain ⟨g1, g2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht h1 h2
  exact AddSubgroup.subset_closure ⟨_, g1, g2, _, htb, GlobalTheory.IdVGen.tmul_eq ht α a⟩

theorem exists_modul {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap D.host.F D.host.E t ∈
      (((P.modul sc * P.modulBar sc : Ideal (𝓞 D.host.E))) : FI D) := by
  classical
  have hu : ∀ u ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ u.asIdeal ∧ t ∉ v.asIdeal := by
    intro u hu
    by_contra hcon
    push_neg at hcon
    have e : u = v := IsDedekindDomain.HeightOneSpectrum.ext
      (u.isMaximal.eq_of_le v.isPrime.ne_top hcon)
    exact hv (e ▸ hu)
  choose! tu htu htv using hu
  let t : 𝓞 D.host.F := ∏ u ∈ P.S0, tu u ^ P.depth sc u
  have htv' : t ∉ v.asIdeal := by
    intro hmem
    obtain ⟨u, hu, hmem'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact htv u hu (v.isPrime.mem_of_pow_mem _ hmem')
  have hmod : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
    simp only [t, map_prod, map_pow, Places.modul]
    refine Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow ?_ _
    have e := P.under_w hu
    have : tu u ∈ ((P.w u).under (𝓞 D.host.F)).asIdeal := by rw [e]; exact htu u hu
    exact this
  have hfix : D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t := by
    apply Subtype.ext
    exact (D.host.conjE_mem_hostF_iff _).1 (t : D.host.F).2
  have hbar : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modulBar sc := by
    rw [← hfix]
    exact Ideal.smul_mem_pointwise_smul _ _ _ hmod
  refine ⟨t * t, v.isPrime.mul_notMem htv' htv', ?_⟩
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mul_mem_mul hmod hbar, ?_⟩
  rw [← map_mul]
  rfl

end GlobalTheory.StairLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairFnUpdateLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem kkV_add (S : GridChoice W U) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ}
    (hf : IsThetaFunO W.ψ _ _ f) (hf' : IsThetaFunO W.ψ _ _ f') (a : FinPt G p.small) (b : FinPt G p.big) :
    kkV S p (f + f') a b = kkV S p f a b + kkV S p f' a b :=
  GlobalTheory.TopZeroInv.kkVec_add S p hf hf' a b

theorem kkV_smul (S : GridChoice W U) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ)
    (a : FinPt G p.small) (b : FinPt G p.big) :
    kkV S p (c • f) a b = c • kkV S p f a b :=
  GlobalTheory.TopZeroInv.kkVec_smul S p c f a b

theorem colV_congr (S : GridChoice W U) {t : T} {v v' : ∀ a, FactorFn G t a} (h : ∀ j, v (.inl j) = v' (.inl j))
    (x : ∀ j, FinPt G (.top j)) : colV S v x = colV S v' x := by
  have e : (fun j => if h : j < D.R.m then kkV S (.top t j) (v (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) =
      (fun j => if h : j < D.R.m then kkV S (.top t j) (v' (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) := by
    funext j; split_ifs with hj
    · rw [h]
    · rfl
  simp only [colV, e]

theorem rowV_congr (S : GridChoice W U) {t : T} {v v' : ∀ a, FactorFn G t a} (h : ∀ i, v (.inr i) = v' (.inr i))
    (y : ∀ i, FinPt G (.grid i D.R.m)) : rowV S v y = rowV S v' y := by
  have e : (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v' (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := by
    funext i; split_ifs with hi
    · rw [h]
    · rfl
  simp only [rowV, e]

theorem colK_update (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m)
    (F : FactorFn G t (.inl j₀)) :
    (fun j => if h : j < D.R.m then kkV S (.top t j) (Function.update v (.inl j₀) F (.inl ⟨j, h⟩)) (x j) (x (j + 1))
      else 0) =
    Function.update (fun j => if h : j < D.R.m then kkV S (.top t j) (v (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) j₀.1
      (kkV S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1))) := by
  funext j
  by_cases hj : j = j₀.1
  · subst hj
    rw [Function.update_self, dite_eq_left j₀.2]
    show kkV S (.top t j₀.1) (Function.update v (.inl j₀) F (.inl j₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hj]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hj (congrArg Fin.val (Sum.inl_injective e))
    · rfl

theorem rowK_update (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    (F : FactorFn G t (.inr i₀)) :
    (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (Function.update v (.inr i₀) F (.inr ⟨i, h⟩)) (y i) (y (i + 1))
      else 0) =
    Function.update (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) i₀.1
      (kkV S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1))) := by
  funext i
  by_cases hi : i = i₀.1
  · subst hi
    rw [Function.update_self, dite_eq_left i₀.2]
    show kkV S (.chi i₀.1 D.R.m) (Function.update v (.inr i₀) F (.inr i₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hi]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hi (congrArg Fin.val (Sum.inr_injective e))
    · rfl

theorem pairFn_apply (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (v : ∀ a, FactorFn G t a) (p : VV ℂ (wt G (.top 0))) (q : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    pairFn S x y v p q =
      brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) (colV S v x p) (rowV S v y q) := rfl

theorem pairFn_update_linear : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (v : ∀ a, FactorFn G t a), (∀ a, v a ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) → ∀ (a : Fin D.R.m ⊕ Fin D.R.m) (f g : FactorFn G t a), f ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) → g ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) → pairFn S x y (Function.update v a (f + g)) = pairFn S x y (Function.update v a f) + pairFn S x y (Function.update v a g) ∧ ∀ c : ℂ, pairFn S x y (Function.update v a (c • f)) = c • pairFn S x y (Function.update v a f) := by
  intro D T L sc G W U S t x y v _ a f g hf hg
  rcases a with j₀ | i₀
  · have hr : ∀ F, rowV S (Function.update v (.inl j₀) F) y = rowV S v y := fun F =>
      rowV_congr S (fun i => Function.update_of_ne Sum.inr_ne_inl _ _) y
    have hadd : colV S (Function.update v (.inl j₀) (f + g)) x =
        colV S (Function.update v (.inl j₀) f) x + colV S (Function.update v (.inl j₀) g) x := by
      have h : kkV S (.top t j₀.1) (f + g) (x j₀.1) (x (j₀.1 + 1)) =
          kkV S (.top t j₀.1) f (x j₀.1) (x (j₀.1 + 1)) + kkV S (.top t j₀.1) g (x j₀.1) (x (j₀.1 + 1)) :=
        kkV_add S (.top t j₀.1) hf hg _ _
      rw [colV, colV, colV, colK_update, colK_update, colK_update, h,
        GlobalTheory.chainTo_update_add _ _ _ _ _ j₀.2, LinearMap.add_comp]
    have hsmul : ∀ c : ℂ, colV S (Function.update v (.inl j₀) (c • f)) x = c • colV S (Function.update v (.inl j₀) f) x := by
      intro c
      have h : kkV S (.top t j₀.1) (c • f) (x j₀.1) (x (j₀.1 + 1)) = c • kkV S (.top t j₀.1) f (x j₀.1) (x (j₀.1 + 1)) :=
        kkV_smul S (.top t j₀.1) c f _ _
      rw [colV, colV, colK_update, colK_update, h, GlobalTheory.ChainSmul.chainTo_update_smul _ _ _ _ _ j₀.2,
        LinearMap.smul_comp]
    refine ⟨?_, fun c => ?_⟩
    · ext p q
      rw [LinearMap.add_apply, LinearMap.add_apply, pairFn_apply, pairFn_apply, pairFn_apply, hr, hr, hr, hadd,
        LinearMap.add_apply]
      exact LinearMap.map_add₂ _ _ _ _
    · ext p q
      rw [LinearMap.smul_apply, LinearMap.smul_apply, pairFn_apply, pairFn_apply, hr, hr, hsmul, LinearMap.smul_apply]
      exact LinearMap.map_smul₂ _ _ _ _
  · have hc : ∀ F, colV S (Function.update v (.inr i₀) F) x = colV S v x := fun F =>
      colV_congr S (fun j => Function.update_of_ne Sum.inl_ne_inr _ _) x
    have hadd : rowV S (Function.update v (.inr i₀) (f + g)) y =
        rowV S (Function.update v (.inr i₀) f) y + rowV S (Function.update v (.inr i₀) g) y := by
      have h : kkV S (.chi i₀.1 D.R.m) (f + g) (y i₀.1) (y (i₀.1 + 1)) =
          kkV S (.chi i₀.1 D.R.m) f (y i₀.1) (y (i₀.1 + 1)) + kkV S (.chi i₀.1 D.R.m) g (y i₀.1) (y (i₀.1 + 1)) :=
        kkV_add S (.chi i₀.1 D.R.m) hf hg _ _
      rw [rowV, rowV, rowV, rowK_update, rowK_update, rowK_update, h,
        GlobalTheory.chainTo_update_add _ _ _ _ _ i₀.2, LinearMap.add_comp]
    have hsmul : ∀ c : ℂ, rowV S (Function.update v (.inr i₀) (c • f)) y = c • rowV S (Function.update v (.inr i₀) f) y := by
      intro c
      have h : kkV S (.chi i₀.1 D.R.m) (c • f) (y i₀.1) (y (i₀.1 + 1)) = c • kkV S (.chi i₀.1 D.R.m) f (y i₀.1) (y (i₀.1 + 1)) :=
        kkV_smul S (.chi i₀.1 D.R.m) c f _ _
      rw [rowV, rowV, rowK_update, rowK_update, h, GlobalTheory.ChainSmul.chainTo_update_smul _ _ _ _ _ i₀.2,
        LinearMap.smul_comp]
    refine ⟨?_, fun c => ?_⟩
    · ext p q
      rw [LinearMap.add_apply, LinearMap.add_apply, pairFn_apply, pairFn_apply, pairFn_apply, hc, hc, hc, hadd,
        LinearMap.add_apply]
      exact map_add _ _ _
    · ext p q
      rw [LinearMap.smul_apply, LinearMap.smul_apply, pairFn_apply, pairFn_apply, hc, hc, hsmul, LinearMap.smul_apply]
      exact map_smul _ _ _

end GlobalTheory.RowVertexInv
end
end

