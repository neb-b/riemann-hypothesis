module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle0003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IsLAddSegmentOfInjectiveOfNotPrecedes
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentProductEquivalence.CsOrderfree
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0671
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0662
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleApply
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.Bundle0003
public import GroundTheory.PAdicHodge.ACrisGalois

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PeelGood
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos PositivityTheory.Exh GlobalTheory.CompanionTheory.ExhGood

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth.ClsOfF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comm_of (hI : Zc.Cos.LUnlinkedIrr k) : Zc.Cos.LUnlinkedComm k :=
  _root_.GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hI

theorem stdCos (hZ : GlobalTheory.Published.SegmentRepresentation) (hI : Zc.Cos.LUnlinkedIrr k) :
    ∀ (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
      ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd) := by
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  intro 𝔪 h N x hd hx
  obtain ⟨Γ, hΓ, hL⟩ := GlobalTheory.T.langlands_factors_dual_reverse_ordered hA (_root_.GlobalTheory.CompanionTheory.SegLDual.lSegDual hA hZ) 𝔪 x hx
  obtain ⟨hd', ⟨e⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA x hd
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.reverse_ordered_product_has_socle hA (_root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ) hI (comm_of hI) Γ (fun a => dualCl (x a)) hd' hΓ hL
  exact _root_.GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr x hd) (isSmooth_prodIrr x hd) (GlobalTheory.T.product_irreducible_finite_length hA x hd) τ
    (hτ.of_equiv (Representation.Equiv.refl _) e.symm)

theorem segCl (Δ : Segment k) : ∃ x : IrrGL (k := k), IsLSeg Δ x.rep := by
  obtain ⟨π, hπ⟩ := _root_.GlobalTheory.CompanionTheory.SegExists.exists_isLSeg PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ
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

end PositivityTheory.Groth.ClsOfF

namespace PositivityTheory.Groth


open ClsOfF in
theorem cls_of (hZ : GlobalTheory.Published.SegmentRepresentation) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hI : Zc.Cos.LUnlinkedIrr k)
    (H : PositivityTheory.Exh.MidP k ∧ PositivityTheory.Exh.RefineP k ∧ PositivityTheory.Exh.SwapP k) : Cls k := by
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨hM, hR, hS⟩ := H
  have hCm : Zc.Cos.LUnlinkedComm k := comm_of hI
  have hF : Zc.LOrderFree k := PositivityTheory.PfEss.Zc2.cs_orderfree hA hCm
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

end PositivityTheory.Groth

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PhiZBijective
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth.GrothendieckPhiBijection

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem ell_phiOf (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) (hJ : JCls k) (hAlt : AltSum k)
    (Lseg : Segment k → IrrGL (k := k)) (hL : ∀ Δ, IsLSeg Δ (Lseg Δ).rep)
    (hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
      phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)))
    (Δ : Segment k) (p : MvPolynomial (Segment k) ℤ) :
    ell Δ (toR.symm (phiOf Lseg p)) = p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    obtain ⟨h, Γ, hΓ⟩ := exists_enum u
    have hm : MvPolynomial.monomial u a = MvPolynomial.C a * ∏ i : Fin h, MvPolynomial.X (Γ i) := by
      rw [prod_X_of_map u Γ hΓ, MvPolynomial.C_mul_monomial, mul_one]
    have hC : phiOf Lseg (MvPolynomial.C a) = (a : R k) := by simp [phiOf]
    rw [hm, map_mul, hC, hprod h _ Γ rfl, ← zsmul_eq_mul, map_zsmul, AddEquiv.symm_apply_apply, map_zsmul,
      ell_prod hA hj hJ hAlt Lseg hL Δ Γ rfl, hΓ, MvPolynomial.coeff_C_mul, prod_X_of_map u Γ hΓ,
      MvPolynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd ((toMultiset_eq_single_iff u Δ).mp h1) h2
    · exact absurd ((toMultiset_eq_single_iff u Δ).mpr h2) h1
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, MvPolynomial.coeff_add, add_mul]

end PositivityTheory.Groth.GrothendieckPhiBijection

namespace PositivityTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]


open GrothendieckPhiBijection in
theorem phiZ_bijective (hk : Steps k) (h1 : TriAut) (h2 : UniTri)
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) (hZ : IsSegmentClass k Z) :
    Function.Bijective (phiOf (k := k) fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) := by
  obtain ⟨Lseg, hL, hbij, hrep, hprod⟩ := phiL_main hk h2
  obtain ⟨hC, -, -, -, -, -, -, -, hJ, hJS, hAlt⟩ := hk
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hx : ∀ Δ : Segment k, ∃ p : MvPolynomial (Segment k) ℤ,
      phiOf Lseg p = toR (sg (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) ∧
        ∀ s ∈ p.support, msupp (Finsupp.toMultiset s) = Δ.ms := by
    intro Δ
    obtain ⟨n, hn⟩ := hC.exh ⟨Δ.len * Δ.d, Z Δ⟩
    obtain ⟨p, hp1, hp2⟩ := hrep n _ hn
    exact ⟨p, hp1, fun s hs => (hp2 s hs).trans (msupp_seg hA hC.jac Z hZ hJS Δ hn)⟩
  choose p hp1 hp2 using hx
  let ψ : MvPolynomial (Segment k) ℤ →+* MvPolynomial (Segment k) ℤ := (MvPolynomial.aeval p).toRingHom
  have hψX : ∀ Δ, ψ (MvPolynomial.X Δ) = p Δ := fun Δ => MvPolynomial.aeval_X p Δ
  have hcomp : (phiOf Lseg).comp ψ = phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, phiOf]
    · intro Δ
      rw [RingHom.comp_apply, hψX, hp1, phiOf_X]
  have hψ : Function.Bijective ψ := by
    apply h1 (Segment k) (fun Δ => Δ.len) ψ
    intro Δ
    have hell := ell_phiOf hA hC.jac hJ hAlt Lseg hL hprod Δ (p Δ)
    rw [hp1, AddEquiv.symm_apply_apply, ell_sg (hJS Z hZ Δ).1 (hJS Z hZ Δ).2] at hell
    have hc : (p Δ).coeff (Finsupp.single Δ 1) = (-1) ^ (Δ.len - 1) := by
      have h' : ((-1 : ℤ) ^ (Δ.len - 1)) * ((-1) ^ (Δ.len - 1)) = 1 := by
        rw [← mul_pow]
        simp
      calc (p Δ).coeff (Finsupp.single Δ 1)
          = (p Δ).coeff (Finsupp.single Δ 1) * ((-1) ^ (Δ.len - 1) * (-1) ^ (Δ.len - 1)) := by
            rw [h', mul_one]
        _ = (-1) ^ (Δ.len - 1) := by rw [← mul_assoc, ← hell, one_mul]
    refine ⟨(-1) ^ (Δ.len - 1), _, vars_lt hA (p Δ) (hp2 Δ), ?_⟩
    rw [hψX, MvPolynomial.X, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    push_cast
    rw [← hc, add_sub_cancel]
  rw [← hcomp]
  exact hbij.comp hψ

end PositivityTheory.Groth

end
end

