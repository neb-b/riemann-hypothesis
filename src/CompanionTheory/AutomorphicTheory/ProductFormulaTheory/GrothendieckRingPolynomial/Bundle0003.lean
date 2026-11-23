module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.Bundle0001
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.Bundle0003
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IsLAddSegmentOfInjectiveOfNotPrecedes
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.Bundle0004
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.SquareIntegrableSegments.SegmentReordering.CsOrderfree
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0056
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SocleOfMultiplicityOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0671
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0662
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleApply
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.Bundle0002

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PeelGood
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos CompanionTheory.Exh GlobalTheory.CompanionTheory.ExhGood

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.ClsOfF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comm_of (hI : Zc.Cos.LUnlinkedIrr k) : Zc.Cos.LUnlinkedComm k :=
  _root_.GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hI

theorem stdCos (hZ : GlobalTheory.Published.SegmentRepresentation) (hI : Zc.Cos.LUnlinkedIrr k) :
    ∀ (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
      ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  intro 𝔪 h N x hd hx
  obtain ⟨Γ, hΓ, hL⟩ := GlobalTheory.T.langlands_factors_dual_reverse_ordered hA (_root_.GlobalTheory.CompanionTheory.SegLDual.lSegDual hA hZ) 𝔪 x hx
  obtain ⟨hd', ⟨e⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA x hd
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.reverse_ordered_product_has_socle hA (_root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ) hI (comm_of hI) Γ (fun a => dualCl (x a)) hd' hΓ hL
  exact _root_.GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr x hd) (isSmooth_prodIrr x hd) (GlobalTheory.T.product_irreducible_finite_length hA x hd) τ
    (hτ.of_equiv (Representation.Equiv.refl _) e.symm)

theorem segCl (Δ : Segment k) : ∃ x : IrrGL (k := k), IsLSeg Δ x.rep := by
  obtain ⟨π, hπ⟩ := _root_.GlobalTheory.CompanionTheory.SegExists.exists_isLSeg CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, hπ.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr)⟩

theorem ex_of (HS : ∀ (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
      ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd)) (𝔪 : Multiset (Segment k)) :
    ∃ x : IrrGL (k := k), IsL 𝔪 x.rep := by
  obtain ⟨Δ, hΔ⟩ := GlobalTheory.LocGL.exists_isOrderedForm 𝔪
  choose y hy using (segCl (k := k))
  let x : Fin 𝔪.card → IrrGL (k := k) := fun i => y (Δ i)
  have hx : LFactors 𝔪 x := ⟨Δ, hΔ, fun i => hy (Δ i)⟩
  obtain ⟨π, hπ⟩ := HS 𝔪 𝔪.card _ x rfl hx
  refine ⟨IrrGL.of π.ρ π.smooth π.irr, 𝔪.card, x, rfl, hx, ?_⟩
  exact hπ.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (.refl _)

theorem peelGood (HS : ∀ (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
      ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd)) (HL : LSocleGL k) : Zc.PeelGoodP k := by
  intro x y hd s 𝔫 hs hn hf hp
  obtain ⟨f, hf⟩ := hf
  have hn' := hn
  obtain ⟨h, z, hz, ⟨Δ, hΔ, hzL⟩, -⟩ := hn'
  let w : Fin (h + 1) → IrrGL (k := k) := Fin.snoc (α := fun _ => IrrGL (k := k)) z (y 0)
  have hwL : LFactors (𝔫 + {s}) w := by
    refine ⟨_, isOrderedForm_snoc hΔ s hp, fun i => ?_⟩
    induction i using Fin.lastCases with
    | last =>
      have e : w (Fin.last h) = y 0 := Fin.snoc_last (α := fun _ => IrrGL (k := k)) _ _
      rw [e, Fin.snoc_last]
      exact hs
    | cast i =>
      have e : w i.castSucc = z i := Fin.snoc_castSucc (α := fun _ => IrrGL (k := k)) _ _ _
      rw [e, Fin.snoc_castSucc]
      exact hzL i
  have hwd : ∑ a, (w a).1 = x.1 := by
    rw [Fin.sum_univ_castSucc, ← hd, Fin.sum_univ_two, add_comm, ← hz]
    simp [w]
  have hwr : ∑ a, (w (Fin.rev a)).1 = x.1 := (Equiv.sum_comp Fin.revPerm fun a => (w a).1).trans hwd
  have hzr : ∑ a, (z (Fin.rev a)).1 = (y 1).1 := (Equiv.sum_comp Fin.revPerm fun a => (z a).1).trans hz
  obtain ⟨π, hπ⟩ := HS (𝔫 + {s}) (h + 1) x.1 w hwd hwL
  have hπL : IsL (𝔫 + {s}) π.ρ := ⟨_, w, hwd, hwL, hπ⟩
  have hsoc := HL (𝔫 + {s}) (h + 1) x.1 w hwr hwL π.ρ hπL
  have hsoc₁ := HL 𝔫 h (y 1).1 z hzr ⟨Δ, hΔ, hzL⟩ (y 1).rep hn
  obtain ⟨-, g, hg, -⟩ := hsoc₁
  obtain ⟨F, hF⟩ := embed_family y (w ∘ Fin.rev) (z ∘ Fin.rev)
    (by simp [w, Function.comp]) (fun i => by simp [w, Function.comp, Fin.rev_succ]) hd hwr hzr g hg
  obtain ⟨e⟩ := hsoc.equiv_of_embeds x.2.rep.irr ⟨F.comp f, hF.comp hf⟩
  exact hπL.of_equiv e.symm

theorem exh_at (hM : MidP k) (hR : RefineP k) (hS : SwapP k) (hC : CuspEmbP k) (hP : SuppP k) (hJ : JuxtP k)
    (hL : LinkP k) (hm : MinP k) (hG : Zc.PeelGoodP k) (x : IrrGL (k := k)) : ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep := by
  suffices H : ∀ n : ℕ, ∀ x : IrrGL (k := k), x.1 = n → ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep from H _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact GlobalTheory.LocGL.exh_le_one x (by omega)
    obtain ⟨l, hl, hx⟩ := hC x
    have hne : l ≠ [] := by
      rintro rfl
      obtain ⟨hd, -⟩ := hx
      simp at hd
      omega
    obtain ⟨ρ, hρ, hmin⟩ := hm l hne hl
    obtain ⟨A, B, rfl⟩ := List.append_of_mem hρ
    obtain ⟨Γ, c, y, e, hc, hy⟩ := move_left hM hR hS hJ hL x ρ A
      (fun a ha => ⟨hl a (List.mem_append_left _ ha), by simpa using hmin a (List.mem_append_left _ ha) 1 one_pos⟩)
      (Segment.single ρ (hl ρ hρ)) ρ B rfl (single_spec (hl ρ hρ)).2.1 (by simpa using hx)
    obtain ⟨hd, f, hf⟩ := id hy
    have hdeg : Γ.deg = c.1 := hc.deg_eq
    have hpos' : 0 < Γ.deg := Nat.mul_pos Γ.len_pos Γ.d_pos
    have hd2 : c.1 + y.1 = x.1 := (Fin.sum_univ_two fun a => ([c, y].get a).1).symm.trans hd
    obtain ⟨𝔫, h𝔫⟩ := ih y.1 (by omega) y rfl
    refine ⟨_, hG x [c, y].get hd Γ 𝔫 hc h𝔫 ⟨f, hf⟩ fun Δ' hΔ' hp => ?_⟩
    obtain ⟨j, hj, ej⟩ := hp.2
    exact hmin _ (hP x c y _ 𝔫 hl hx hy h𝔫 Δ' hΔ') j hj (e.symm.trans ej)

end CompanionTheory.Groth.ClsOfF

namespace CompanionTheory.Groth


open ClsOfF in
theorem cls_of (hZ : GlobalTheory.Published.SegmentRepresentation) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hI : Zc.Cos.LUnlinkedIrr k)
    (H : CompanionTheory.Exh.MidP k ∧ CompanionTheory.Exh.RefineP k ∧ CompanionTheory.Exh.SwapP k) : Cls k := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨hM, hR, hS⟩ := H
  have hCm : Zc.Cos.LUnlinkedComm k := comm_of hI
  have hF : Zc.LOrderFree k := CompanionTheory.PfEss.Zc2.cs_orderfree hA hCm
  have hSoc : Zc.LSocleGL k := _root_.GlobalTheory.CompanionTheory.LSocle.lSocleGL hA (_root_.GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) hF
  have HS := stdCos hZ hI
  have hC : CuspEmbP k := cuspEmbP k hA hR
  exact
    { ex := ex_of HS
      exh := exh_at hM hR hS hC (suppP k)
        (juxtP_of_fineUniq hA hM hR hS hC (GlobalTheory.T.segment_product_word_in_shuffle hA (_root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ)) (_root_.GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec hA hZ))
        linkP minP (peelGood HS hSoc)
      free := hF
      soc := hSoc
      jac := _root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ
      seg := fun Δ => _root_.GlobalTheory.CompanionTheory.SegExists.exists_isLSeg hA Δ
      unl := hI
      com := hCm }

end CompanionTheory.Groth

end
end

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PhiZBijective
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.GrothendieckPhiBijection

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem ell_phiOf (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) (hJ : JCls k) (hAlt : AltSum k)
    (Lseg : Segment k → IrrGL (k := k)) (hL : ∀ Δ, IsLSeg Δ (Lseg Δ).rep)
    (hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
      phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)))
    (Δ : Segment k) (p : MvPolynomial (Segment k) ℤ) :
    ell Δ (toR.symm (phiOf Lseg p)) = p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) := by
  classical
  have hm : ∀ s : Segment k →₀ ℕ, ell Δ (toR.symm (phiOf Lseg (MvPolynomial.monomial s 1))) =
      if s = Finsupp.single Δ 1 then (-1) ^ (Δ.len - 1) else 0 := by
    intro s
    obtain ⟨h, Γ, hΓ⟩ := exists_enum s
    rw [← prod_X_of_map s Γ hΓ, hprod h _ Γ rfl, AddEquiv.symm_apply_apply, ell_prod hA hj hJ hAlt Lseg hL, hΓ]
    by_cases hs : s = Finsupp.single Δ 1
    · rw [if_pos ((toMultiset_eq_single_iff s Δ).2 hs), if_pos hs]
    · rw [if_neg (fun h => hs ((toMultiset_eq_single_iff s Δ).1 h)), if_neg hs]
  have hm' : ∀ v, ell Δ (toR.symm (phiOf Lseg (MvPolynomial.monomial v (p.coeff v)))) =
      p.coeff v * (if v = Finsupp.single Δ 1 then (-1) ^ (Δ.len - 1) else 0) := by
    intro v
    have : MvPolynomial.monomial v (p.coeff v) = p.coeff v • MvPolynomial.monomial v (1 : ℤ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_zsmul, map_zsmul, map_zsmul, hm, smul_eq_mul]
  conv_lhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hm']
  rw [Finset.sum_eq_single (Finsupp.single Δ 1)]
  · simp
  · intro b _ hb; simp [hb]
  · intro hn; rw [MvPolynomial.notMem_support_iff.1 hn]; simp

end CompanionTheory.Groth.GrothendieckPhiBijection

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]


open GrothendieckPhiBijection in
theorem phiZ_bijective (hk : Steps k) (h1 : TriAut) (h2 : UniTri)
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) (hZ : IsSegmentClass k Z) :
    Function.Bijective (phiOf (k := k) fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨Lseg, hL, hbij, hpre, hprod⟩ := phiL_main hk h2
  obtain ⟨hcls, -, -, -, -, -, -, -, hJ, hS, hAlt⟩ := hk
  have key : ∀ Δ : Segment k, ∃ p : MvPolynomial (Segment k) ℤ,
      phiOf Lseg p = toR (sg (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) ∧
      ∃ (ε : ℤˣ) (q : MvPolynomial (Segment k) ℤ), (∀ t ∈ q.vars, t.len < Δ.len) ∧
        p = (ε : ℤ) • MvPolynomial.X Δ + q := by
    intro Δ
    obtain ⟨𝔫, h𝔫⟩ := hcls.exh ⟨Δ.len * Δ.d, Z Δ⟩
    obtain ⟨p, hp, hsupp⟩ := hpre 𝔫 _ h𝔫
    have hms := msupp_seg hA hcls.jac Z hZ hS Δ h𝔫
    have hce : p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) = 1 := by
      rw [← ell_phiOf hA hcls.jac hJ hAlt Lseg hL hprod Δ p, hp, AddEquiv.symm_apply_apply,
        ell_sg (hS Z hZ Δ).1 (hS Z hZ Δ).2]
    have hc : p.coeff (Finsupp.single Δ 1) = (-1) ^ (Δ.len - 1) := by
      have hsq : ((-1 : ℤ) ^ (Δ.len - 1)) * (-1) ^ (Δ.len - 1) = 1 := by
        rw [← mul_pow]; norm_num
      calc p.coeff (Finsupp.single Δ 1)
          = p.coeff (Finsupp.single Δ 1) * ((-1) ^ (Δ.len - 1) * (-1) ^ (Δ.len - 1)) := by rw [hsq, mul_one]
        _ = (-1) ^ (Δ.len - 1) := by rw [← mul_assoc, hce, one_mul]
    refine ⟨p, hp, (-1) ^ (Δ.len - 1),
      p - MvPolynomial.monomial (Finsupp.single Δ 1) (p.coeff (Finsupp.single Δ 1)),
      vars_lt hA p (fun s hs => (hsupp s hs).trans hms), ?_⟩
    have hX : (((-1 : ℤˣ) ^ (Δ.len - 1) : ℤˣ) : ℤ) • (MvPolynomial.X Δ : MvPolynomial (Segment k) ℤ) =
        MvPolynomial.monomial (Finsupp.single Δ 1) (p.coeff (Finsupp.single Δ 1)) := by
      rw [hc, MvPolynomial.X, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      push_cast
      rfl
    rw [hX]
    ring
  choose p hp ε q hq hpq using key
  have hψ : Function.Bijective (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p) :=
    h1 (Segment k) Segment.len _ fun Δ => ⟨ε Δ, q Δ, hq Δ, by rw [MvPolynomial.eval₂Hom_X']; exact hpq Δ⟩
  have heq : phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) =
      (phiOf Lseg).comp (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int ((phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩)).comp MvPolynomial.C)
        (((phiOf Lseg).comp (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p)).comp
          MvPolynomial.C)) r
    · intro Δ
      rw [phiOf_X, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', hp Δ]
  rw [heq]
  exact hbij.comp hψ

end CompanionTheory.Groth

end
end

