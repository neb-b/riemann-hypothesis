module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.TrueCx.PointWell

open Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem moeb_one {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) : moeb 1 z = z := by
  rw [← fromBlocks_one, moeb, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem block_of_moeb_eq {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hx' : x' ∈ X.dom) (τ : X.Ψ) (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) (a b : Fin r)
    (ha : X.p0 ≤ a) (hb : (b : ℕ) < X.p0) : ((mat x τ)⁻¹ * mat x' τ) a b = 0 := by
  have hu := frameCo_isUnit₂₂ X hj hp hx τ
  have hu' := frameCo_isUnit₂₂ X hj hp hx' τ
  have hd : IsUnit (mat x τ).det := (hx τ).1.isUnit
  have hd0 : IsUnit (mat (x0F X) τ).det := (det_x0F X τ).isUnit
  have hN : (frameCo X hj x τ)⁻¹ * frameCo X hj x' τ = reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
    simp only [frameCo, inv_reindex]
    simp only [reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hd0, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd0]
  have hf : IsUnit (frameCo X hj x τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ hd0).mul hd
  rw [moeb_zero, moeb_zero] at h
  generalize frameCo X hj x τ = f at *
  generalize frameCo X hj x' τ = f' at *
  have h1 : f'.toCols₂ = f * fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂) := by
    have h0 := fromBlocks_mul_fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂)
      f.toBlocks₁₁ f.toBlocks₁₂ f.toBlocks₂₁ f.toBlocks₂₂
    rw [fromBlocks_toBlocks] at h0
    refine Eq.trans ?_ h0.symm
    simp only [Matrix.mul_zero, zero_add]
    rw [mul_nonsing_inv_cancel_left _ _ hu, ← Matrix.mul_assoc, h, nonsing_inv_mul_cancel_right _ _ hu']
    ext (a | a) b <;> rfl
  have h2 : (f⁻¹ * f').toCols₂ = fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂) :=
    (congrArg (f⁻¹ * ·) h1).trans (nonsing_inv_mul_cancel_left f _ hf)
  have hb' : (b : ℕ) < r - j := hp ▸ hb
  have ha' : (a : ℕ) - (r - j) < j := by have := a.2; omega
  have h3 := congrFun (congrFun h2 (Sum.inl ⟨_, ha'⟩)) ⟨_, hb'⟩
  rw [hN] at h3
  have ea : (idx hj).symm (Sum.inl ⟨_, ha'⟩) = a := Fin.ext (by rw [idx_symm_inl]; simp only; omega)
  have eb : (idx hj).symm (Sum.inr ⟨_, hb'⟩) = b := Fin.ext (by rw [idx_symm_inr])
  simpa [toCols₂, ea, eb] using h3

theorem perFr_mem {A : Type} (S : Submodule ℂ (A → ℂ)) (w : A → Fin r → E) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h1 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x τ)⁻¹ * mat x' τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x' τ)⁻¹ * mat x τ) a b = 0)
    (τ : E →+* ℂ) (m : ℕ) (hm : τ ∈ X.Ψ → m = r - X.p0) (hm' : τ ∉ X.Ψ → m = X.p0)
    (hS : ∀ i < m, (fun a => perFr X x (w a) τ i) ∈ S) (i : ℕ) (hi : i < m) :
    (fun a => perFr X x' (w a) τ i) ∈ S := by
  have hp := X.p0_le
  by_cases h : τ ∈ X.Ψ
  · have hm := hm h
    have hd : IsUnit (mat x ⟨τ, h⟩).det := (hx _).1.isUnit
    have hi' : X.p0 + i < r := by omega
    have key : (∑ b : Fin r, ((mat x' ⟨τ, h⟩)⁻¹ * mat x ⟨τ, h⟩) ⟨_, hi'⟩ b •
        fun a => ((mat x ⟨τ, h⟩)⁻¹.mulVec (Data.emb τ (w a))) b) ∈ S := by
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < X.p0
      · rw [h2 _ _ _ (Nat.le_add_right _ _) hb, zero_smul]; exact zero_mem _
      · refine Submodule.smul_mem _ _ ?_
        have hbr := b.2
        convert hS (b - X.p0) (by omega) using 2 with a
        unfold perFr
        rw [dite_eq_left h, dite_eq_left (by omega)]
        congr 1
        exact Fin.ext (by simp; omega)
    convert key using 2 with a
    unfold perFr
    rw [dite_eq_left h, dite_eq_left hi']
    conv_lhs => rw [← mul_nonsing_inv_cancel_right (mat x ⟨τ, h⟩) (mat x' ⟨τ, h⟩)⁻¹ hd, ← mulVec_mulVec]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  · have hm := hm' h
    have h' : conjEmb τ ∈ X.Ψ := by_contra fun h' => h ((X.cmType τ).2 h')
    have hd : IsUnit (mat x ⟨_, h'⟩).det := (hx _).1.isUnit
    have hi' : X.p0 - 1 - i < r := by omega
    have key : (∑ b : Fin r, ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) b ⟨_, hi'⟩ •
        fun a => hermC (conjEmb τ) X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (mat x ⟨_, h'⟩) b) (Data.emb (conjEmb τ) (w a))) ∈ S := by
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < X.p0
      · refine Submodule.smul_mem _ _ ?_
        convert hS (X.p0 - 1 - b) (by omega) using 2 with a
        unfold perFr
        rw [dite_eq_right h, dite_eq_left h', dite_eq_left (by omega)]
        congr 2
        exact Fin.ext (by simp; omega)
      · rw [h1 _ _ _ (not_lt.1 hb) (by simp only; omega), zero_smul]; exact zero_mem _
    convert key using 2 with a
    unfold perFr
    rw [dite_eq_right h, dite_eq_left h', dite_eq_left hi']
    conv_lhs => rw [← mul_nonsing_inv_cancel_left (mat x ⟨_, h'⟩) (mat x' ⟨_, h'⟩) hd]
    generalize (mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩ = n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (f := fun b c => ∑ d, n b _ * _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}
  {U : Unf Xo c σ r}

theorem pt_eq_of_block (hU : IsUnf U) (hσ : GoodEmb c σ) (k : U.Comp) (x x' : (U.X k).dom)
    (h1 : ∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x.1 τ)⁻¹ * mat x'.1 τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x'.1 τ)⁻¹ * mat x.1 τ) a b = 0) :
    (U.un k x).x = (U.un k x').x := by
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hF⟩ := hU
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hty k
  obtain ⟨P, hP, hper, hx, -⟩ := hF k x
  obtain ⟨P', hP', hper', hx', -⟩ := hF k x'
  have hmem : ∀ j, (fun a => P' a j) ∈ Submodule.span ℂ (Set.range fun (j : Fin g) a => P a j) := by
    intro j
    simp only [hP']
    refine perFr_mem (U.X k) _ (fun a => (φ k a : Fin r → E)) x.2 h1 h2 _ (Dw.mult (e j).1) (fun h => ?_)
      (fun h => ?_) (fun i hi => ?_) _ (e j).2.2
    · exact (if_pos ((hrt _).1 ((hty _).1 h))).trans (by omega)
    · exact (if_neg (fun h' => h ((hty _).2 ((hrt _).2 h')))).trans hp0.symm
    · refine Submodule.subset_span ⟨e.symm ⟨(e j).1, ⟨i, hi⟩⟩, funext fun a => ?_⟩
      dsimp only
      rw [hP, Equiv.apply_symm_apply]
  choose μ hμ using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem j)
  have hL : ∀ a, P' a = mulVecLin (of μ) (P a) := fun a => funext fun j => by
    have := congrFun (hμ j) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    rfl
  have hsurj : Function.Surjective (mulVecLin (of μ)) := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range P') := by rw [hper'.2.2.2.1]; trivial
    refine (Submodule.span_le (p := (LinearMap.range (mulVecLin (of μ))).restrictScalars ℝ)).2 ?_ hy
    rintro _ ⟨a, rfl⟩
    exact ⟨P a, (hL a).symm⟩
  rw [hx, hx']
  exact (F.fibre _ P P' hper hper').2 ⟨LinearEquiv.refl _ _,
    LinearEquiv.ofBijective _ ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩, fun _ _ => rfl,
    fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hL⟩

end GlobalTheory.TrueCx.PointWell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingCoordinatewiseImageEqExtendedData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LiftRead

theorem read_of_span {L L' : Type} [Field L] [Field L'] (φ : L →+* L') (σ : L →+* ℂ) (σ' : L' →+* ℂ) (hφ : ∀ x, σ' (φ x) = σ x)
    {n n' : ℕ} (hn : n = n') {H H' : Type} (nH : NormedAddCommGroup H) (nH' : NormedAddCommGroup H')
    (iH : InnerProductSpace ℂ H) (iH' : InnerProductSpace ℂ H') (hH : H' = H) (h1 : HEq nH' nH) (h2 : HEq iH' iH)
    (j : (Fin n → L) →ₛₗ[σ] H) (j' : (Fin n' → L') →ₛₗ[σ'] H') (S : Set (Fin n → L)) (hS : Submodule.span L S = ⊤)
    (hj : ∀ y ∈ S, ∃ y' : Fin n' → L', (∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → σ' (y' k') = σ (y k)) ∧ HEq (j' y') (j y))
    (x : Fin n → L) (x' : Fin n' → L') (hx : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)) :
    HEq (j' x') (j x) := by
  subst hn hH
  cases h1
  cases h2
  have e : x' = fun k => φ (x k) := funext fun k => hx k k rfl
  subst e
  clear hx
  refine heq_of_eq ?_
  have hx : x ∈ Submodule.span L S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y', a, b⟩ := hj y hy
    have e : (fun k => φ (y k)) = y' := funext fun k => σ'.injective ((hφ _).trans (a k k rfl).symm)
    rw [e]
    exact eq_of_heq b
  | zero =>
    have e : (fun k => φ ((0 : Fin n → L) k)) = 0 := by funext k; simp
    rw [e, map_zero, map_zero]
  | add y z _ _ hy hz =>
    have e : (fun k => φ ((y + z) k)) = (fun k => φ (y k)) + fun k => φ (z k) := by funext k; simp
    rw [e, map_add (f := _), map_add (f := _), hy, hz]
  | smul a y _ hy =>
    have e : (fun k => φ ((a • y) k)) = φ a • fun k => φ (y k) := by funext k; simp
    rw [e, map_smulₛₗ, map_smulₛₗ, hy, hφ]


set_option maxHeartbeats 4000000 in
theorem hmod_fields {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt}
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) (X : HMod (Formalism.IndefR.Mult.MMap M)) (X' : HMod (Formalism.IndefR.Mult.MMap M')) (hX : HEq X' X) :
    X'.H = X.H ∧ HEq X'.nH X.nH ∧ HEq X'.iH X.iH := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  have e' : X' = X := eq_of_heq hX
  subst e'
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩


set_option maxHeartbeats 4000000 in
theorem read_extN {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (hE : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hx : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) :
    HEq ((z'.R.FW j').j (w'.st Z').toD7.what₂.embLL x') ((z.R.FW j).j (w.st Z).toD7.what₂.embLL x) := by
  have hk := hE.κ j j' hj
  have hc : ↥(z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n) =
      ↥(z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n) := (by with_unfolding_all exact ((cusp_type_congr (P₁ := B.toPre) (P₂ := B'.toPre) q (congrArg (· + 1) hj) hk.2.2
      hE.H hE.l hE.c hE.Dw hE.Xo hE.U hk.1 hk.2.1) :))
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) q
  have hn : z.R.nW j = z'.R.nW j' := GlobalTheory.Mem.R3.LiftForms.nat_eq_of_heq hm hE.nW j j' hj
  obtain ⟨a, b, c, d, l, e, g, -, hW, -, hr⟩ := hE.MW j j' hj
  obtain ⟨h0, h1, h2⟩ := hmod_fields q j j' hj _ _ a b c d l e g _ _ hW
  obtain ⟨m, bs, hb, -, -, -, hsp⟩ := z.geo.fw.ks j
  refine read_of_span φ _ _ hφ hn _ _ _ _ h0 h1 h2 _ _ (Set.range bs) hsp ?_ x x' hx
  rintro _ ⟨i, rfl⟩
  obtain ⟨u, hu⟩ := (z.geo.fw.e j).surjective ⟨bs i, hb i⟩
  have hu' : bs i = (z.geo.fw.e j u : (z.R.FW j).WK).1 := (congrArg Subtype.val hu).symm
  rw [hu']
  exact ⟨(z'.geo.fw.e j' (cast hc.symm u) : (z'.R.FW j').WK).1, hE.forms j j' hj u _ (cast_heq _ _), hr u _ (cast_heq _ _)⟩


set_option maxHeartbeats 2000000 in
theorem read_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL), (∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) → HEq ((z'.R.FW j').j (w'.st Z').toD7.what₂.embLL x') ((z.R.FW j).j (w.st Z).toD7.what₂.embLL x)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hExt j j' hj φ hφ x x' hx => ?_
  exact read_extN hE.1 hExt j j' hj φ hφ x x' hx

end GlobalTheory.Mem.R3.LiftRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTrans
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StdTr

theorem heq_fin_apply {m m' : ℕ} {f : Fin m → ℕ} {g : Fin m' → ℕ} (h : HEq g f) (hm : m' = m) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') : g i' = f i := by
  subst hm
  cases h
  exact congrArg g (Fin.ext hi.symm)

theorem heq_fin_mid {m m' : ℕ} {f : Fin m → ℕ} {g : Fin m' → ℕ} (h : HEq g f) (hm : m' = m) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') (k : Fin (f i)) : ∃ k' : Fin (g i'), (k : ℕ) = k' :=
  ⟨⟨k, lt_of_lt_of_eq k.2 (heq_fin_apply h hm i i' hi).symm⟩, rfl⟩

theorem heq_mid {α β : Type} (h : β = α) (a : α) : ∃ b : β, HEq b a := ⟨cast h.symm a, cast_heq _ _⟩


set_option maxHeartbeats 1000000 in
theorem ext_trans {B₁ B₂ B₃ : Base} {f₁ f₂ f₃ T₁ T₂ T₃} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {w₃ : ColW B₃ f₃ T₃} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {Z₃ : w₃.Lt} {h₁ h₂ h₃ W₁ W₂ W₃} {z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁} {z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂} {z₃ : Dat (w₃.st Z₃) w₃.I h₃ T₃ W₃} (e₁₂ : Enl B₁ B₂) (e₂₃ : Enl B₂ B₃) (x : Ext z₁ z₂) (y : Ext z₂ z₃) :
    Ext z₁ z₃ := by
  have hmm : (w₂.st Z₂).toD7.R.m = (w₁.st Z₁).toD7.R.m := congrArg (fun P : Pre => P.R.m) e₁₂.1
  have hm : ∀ i : Fin (w₁.st Z₁).toD7.R.m, ∃ i' : Fin (w₂.st Z₂).toD7.R.m, (i : ℕ) = i' :=
    fun i => ⟨⟨i, lt_of_lt_of_eq i.2 hmm.symm⟩, rfl⟩
  refine @Ext.mk B₁ B₃ f₁ f₃ T₁ T₃ w₁ w₃ Z₁ Z₃ h₁ h₃ W₁ W₃ z₁ z₃ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact HEq.trans y.H x.H
  · exact HEq.trans y.l x.l
  · exact HEq.trans y.c x.c
  · exact HEq.trans y.Dw x.Dw
  · exact HEq.trans y.Xo x.Xo
  · exact HEq.trans y.U x.U
  · exact HEq.trans y.V x.V
  · exact HEq.trans y.dict x.dict
  · exact HEq.trans y.mu x.mu
  · exact HEq.trans y.Kf x.Kf
  · exact HEq.trans y.cE x.cE
  · exact HEq.trans y.chiW x.chiW
  · exact HEq.trans y.x₀ x.x₀
  · exact HEq.trans y.iota x.iota
  · exact HEq.trans y.ψ x.ψ
  · exact HEq.trans y.θ x.θ
  · exact HEq.trans y.βW x.βW
  · exact HEq.trans y.βY x.βY
  · exact HEq.trans y.nW x.nW
  · exact HEq.trans y.βV x.βV
  · exact HEq.trans y.ΛV x.ΛV
  · exact HEq.trans y.ΛW x.ΛW
  · exact HEq.trans y.Pg x.Pg
  · exact HEq.trans y.eG x.eG
  · exact HEq.trans y.Sb x.Sb
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.BV i i' hi'
    have b := y.BV i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.1 a.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.1 a.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.1 a.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.1 a.2.2.2.2.1
    exact HEq.trans b.2.2.2.2.2 a.2.2.2.2.2
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.MW i i' hi'
    have b := y.MW i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.1) (a.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.1) (a.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.1) (a.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.1) (a.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.1) (a.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.1) (a.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.2.2.2.1)
    intro φ φ'' hφ
    refine Exists.elim (heq_mid (_root_.GlobalTheory.Mem.R3.Rw.Ext.cuspA_type_eq z₁ z₂ e₁₂ x i i' hi') φ) fun φ' hφ' => ?_
    exact HEq.trans (b.2.2.2.2.2.2.2.2.2.2 φ' φ'' (HEq.trans hφ hφ'.symm)) (a.2.2.2.2.2.2.2.2.2.2 φ φ' hφ')
  · intro i i'' h φ φ'' hφ k k'' hk
    refine Exists.elim (hm i) fun i' hi' => ?_
    refine Exists.elim (heq_mid (_root_.GlobalTheory.Mem.R3.Rw.Ext.cuspA_type_eq z₁ z₂ e₁₂ x i i' hi') φ) fun φ' hφ' => ?_
    refine Exists.elim (heq_fin_mid x.nW hmm i i' hi' k) fun k' hk' => ?_
    exact Eq.trans (y.forms i' i'' (hi'.symm.trans h) φ' φ'' (HEq.trans hφ hφ'.symm) k' k'' (hk'.symm.trans hk)) (x.forms i i' hi' φ φ' hφ' k k' hk')
  · intro v v'' hB
    refine Exists.elim (_root_.GlobalTheory.Mem.Top.Bl.exists_below_between (w₁.D Z₁) (w₂.D Z₂) (w₃.D Z₃) e₂₃.2.2.2 v v'' hB) fun v' h => ?_
    exact Iff.trans (x.W1 v v' h.1) (y.W1 v' v'' h.2)
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.cV i i' hi'
    have b := y.cV i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    exact HEq.trans b.2 a.2
  · exact HEq.trans y.pb x.pb
  · exact HEq.trans y.ΛY x.ΛY
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.κ i i' hi'
    have b := y.κ i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.1 a.2.1
    exact Eq.trans b.2.2 a.2.2
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.ref i i' hi'
    have b := y.ref i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.1 a.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.1 a.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.1 a.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.1 a.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.2.1 a.2.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.2.2.1 a.2.2.2.2.2.2.1
    exact HEq.trans b.2.2.2.2.2.2.2 a.2.2.2.2.2.2.2
  · intro i i'' h ok ok'' φ φ'' C
    refine Exists.elim (hm i) fun i' hi' => ?_
    have hv : HEq (B₂.primes w₂.px).vGs (B₁.primes w₁.px).vGs := by
      have a := heq_of_eq z₂.lev.Pg.symm
      have b := heq_of_eq z₁.lev.Pg
      exact HEq.trans (HEq.trans a x.Pg) b
    have L := GlobalTheory.T.referenceTupleLiftForms_pass_to_coeffEnlargement w₁ w₂ W₁ W₂ e₁₂ hv (_root_.GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi_ext z₁ z₂ e₁₂ x) ((i : ℕ) + 1) ((i' : ℕ) + 1) (congrArg (· + 1) hi')
    refine Exists.elim (L.2 φ) fun φ' C' => ?_
    have ok' : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 ((i' : ℕ) + 1)).Ok := Formalism.L2.Col.mtKOk _ _ _ _ h₂ _
    have a := x.jL i i' hi' ok ok' φ φ' C'
    have b := y.jL i' i'' (hi'.symm.trans h) ok' ok'' φ' φ'' fun d' d'' hd => by
      refine Exists.elim (heq_mid L.1.symm d') fun d hd' => ?_
      exact HEq.trans (C d d'' (HEq.trans hd hd'.symm)) (HEq.symm (C' d d' hd'.symm))
    exact HEq.trans b a

theorem std_copy_and_ext_trans : (∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w.st Z') w.I hX T Wt), z'.Xg = z.Xg → z'.tr = z.tr → HEq z'.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := z.alg) z.R) → HEq z'.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.core) → z.Std → z'.Std) ∧ ∀ (B₁ B₂ B₃ : Base) f₁ f₂ f₃ T₁ T₂ T₃ (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (w₃ : ColW B₃ f₃ T₃) (Z₁ : w₁.Lt) (Z₂ : w₂.Lt) (Z₃ : w₃.Lt) h₁ h₂ h₃ W₁ W₂ W₃ (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂) (z₃ : Dat (w₃.st Z₃) w₃.I h₃ T₃ W₃), Enl B₁ B₂ → Enl B₂ B₃ → Ext z₁ z₂ → Ext z₂ z₃ → Ext z₁ z₃ :=
  ⟨std_copy, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁₂ e₂₃ x y => ext_trans e₁₂ e₂₃ x y⟩

end GlobalTheory.Mem.R3.Rw.StdTr
end

