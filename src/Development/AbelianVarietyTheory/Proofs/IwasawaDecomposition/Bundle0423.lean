module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UfGLRatHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0007
public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainFormsRationalIffFrameValues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.RowTie

theorem ptEmb_iff_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ z : (I.per l u a).Wrow, (∃ x, (I.fm l u a).ptEmb x = z) ↔ z ∈ (I.fm l u a).ptC ∧ ∀ c, ∃ Pc ∈ RatSpan (I.rec7 l Z) (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) 1 Pc := by
  intro B X I hI hP l Z u a z
  have hsg : sgTG (D := I.rec7 l Z) (I.fm l u a) = (I.perIn u a).sgT := by
    funext τ
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (k + 1) := by
      rw [hk, show B.R.m * (2 * k + 1 + 1) = 2 * (B.R.m * (k + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = k + 1 := by omega
    show Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) =
      GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := congrArg shiftOf hsg
  exact rat_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT (l.fmL u a).famP (VV_shW B.wts.sgW _) hsh z

end GlobalTheory.Mem.Col2.TwP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleIntegralFormsRowPlaceByPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwLat

open GlobalTheory.Mem.Col2.RowTie

theorem natW_shW' {N : ℕ} (l : DomWeight N) (c : ℤ) : (GlobalTheory.Mem.Col2.shW l c).natW = l.natW := by
  funext i
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.2
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos hN, GlobalTheory.Mem.Col2.shW]
  congr 1
  ring

theorem delStd_shW' {K ι : Type} [Field K] [NumberField K] [Fintype ι] {N : ℕ} (lam : ι → DomWeight N) (c : ℤ) :
    delStd K (fun τ => GlobalTheory.Mem.Col2.shW (lam τ) c) = delStd K lam := by
  unfold delStd delSq
  simp only [natW_shW']

section Gen

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok)

theorem locW_lat_iff (hS : S.Ok) {G : ι → Matrix (Fin n) (Fin n) ℂ} {sh : ι → ℤ} (hsh : sh = shiftOf lam) {e : ι → E →+* ℂ}
    (he : e = embAt σ emb) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
    (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) (w : Pl.Pl)
    (Sp : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ))
    (hSp : ∀ Q, Q ∈ Sp ↔ ∃ z₀ ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delStd K lam), Q = MvPolynomial.map σ z₀)
    (lat : S.Cl → Submodule (𝓞 E) (Fin n → E)) (hlat : ∀ c, S.Lsh c.1 (S.rep c) = lat c)
    (hspan : ∀ c, Submodule.span E (lat c : Set (Fin n → E)) = ⊤) (x : (S.hlat emb lam h).V) :
    x ∈ locW Pl w (S.hlat emb lam h).L ↔ ∀ (c : S.Cl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (lat c : Set _) B →
      ∃ Q ∈ Sp, (show Frames G → ℂ from S.embF emb σ lam h x c) =
        fnOf G sh (Formalism.L2.Forms.atInf e (B⁻¹ : GL (Fin n) E).1) Q := by
  subst hsh he
  have hL : ∀ c, Submodule.IsLattice E (lat c) := fun c => hlat c ▸ hS.lsh_lat c.1 _
  have hfull : ∀ c, Submodule.IsFullLattice E (lat c) := fun c =>
    { toIsLattice := hL c, span_eq_top := hspan c }
  have key : ∀ (c : S.Cl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (lat c : Set _) B →
      (x.1 c ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam (lat c)) ↔
      ∃ Q ∈ Sp, (show Frames G → ℂ from S.embF emb σ lam h x c) =
        fnOf G (shiftOf lam) (Formalism.L2.Forms.atInf (embAt σ emb) (B⁻¹ : GL (Fin n) E).1) Q) := by
    intro c B hB
    refine (BwLat.mem_localization_delAtr_fn emb σ lam (pw w) (by first | exact hfull c | exact (hfull c).toIsLattice) (fun _ => B) (fun τ => BwLat.isBasisAt_of_isLocBasis
      (Pl.resChar_prime w) _ ((bc_mem_below _ _ _).2 (by rw [map_natCast]; exact Formalism.L2.Col.vl_resChar_mem Pl pw hval w)) hB)
      (x.1 c)).trans ⟨?_, ?_⟩
    · rintro ⟨z, hz, e⟩
      exact ⟨_, (hSp _).2 ⟨z, hz, rfl⟩, e⟩
    · rintro ⟨Q, hQ, e⟩
      obtain ⟨z, hz, rfl⟩ := (hSp Q).1 hQ
      exact ⟨z, hz, e⟩
  rw [GlobalTheory.Mem.Col2.mem_locW_hlat_iff emb Pl pw hval S lam h hS w x]
  simp only [hlat]
  unfold locW
  simp only [Formalism.L2.Col.vl_mem_span_intW_iff Pl pw hval w]
  refine ⟨fun H c B hB => (key c B hB).1 (H c), fun H c => ?_⟩
  haveI : Fact (Pl.resChar w).Prime := ⟨Pl.resChar_prime w⟩
  obtain ⟨B, hB⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (Pl.resChar w) E _ (hL c).fg (hspan c)
  exact (key c B hB).2 (H c B hB)

end Gen

end GlobalTheory.Mem.Col2.TwLat

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.Mem.Col2.RowTie GlobalTheory.Mem.Col2.TwLat


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem tw_lat_at : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ w, Formalism.L2.Forms.okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T w → ∀ x : (I.fm l u a).ptLat.V, x ∈ (I.fm l u a).SP w ↔ ∀ (c : (I.fm l u a).clsP) (Bm : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (I.rec7 l Z).host.E), IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (K.lat c : Set _) Bm → ∃ Pc ∈ IntSpan (I.rec7 l Z) w (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a ((I.fm l u a).ptEmb x) c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (I.rec7 l Z).host.E).1) Pc := by
  intro B X I hI hP l Z u a Q K hQ hQT hK w hw x
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hsg : (I.perIn u a).sgT = sgTG (D := I.rec7 l Z) (I.fm l u a) := by
    funext τ
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (k + 1) := by
      rw [hk, show B.R.m * (2 * k + 1 + 1) = 2 * (B.R.m * (k + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = k + 1 := by omega
    show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
      Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := congrArg shiftOf hsg.symm
  have hS : (I.stX a).Ok := (l.per u a).step
  exact locW_lat_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT (l.fmL u a).famP hS hsh hemb
    (I.rec7 l Z).what₂.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq w (IntSpan (I.rec7 l Z) w B.wts.sgW)
    (fun Q => by
      have h := GlobalTheory.LvT.Built.ValLat.mem_closure_iff B.embLL ((I.rec7 l Z).plEq w) (intW (I.rec7 l Z).what₂.places w)
        ((I.rec7 l Z).val_nonneg_iff w) B.wts.sgW Q
      rw [← delStd_shW' B.wts.sgW (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))] at h
      exact h)
    K.lat (fun c => (RowTie.Lsh_empty _).trans (hK.lat c).symm) (fun c => by
      have hG := Formalism.UG.P.csGlob_lattice (F := (I.rec7 l Z).host.F) K.lev.Lb K.lev.Lb_fin K.lev.Lb_span (K.y c).1
      rw [eq_top_iff, ← hG.span_eq_top, Submodule.span_le]
      intro z hz
      exact Formalism.L2.GlobalTheoryTheory.Br.latS_mem_span (F := (I.rec7 l Z).host.F) _ z ((K.y_lat c _).2 hz)) x

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedEmbeddingMatrixSubstitutionMemRatSpan
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

theorem twSub_eq_subP (D : D7) {n : ℕ} (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :
    twSub (embT D) M s P = C (∏ τ, (embT D τ (M : Matrix (Fin n) (Fin n) D.host.E).det) ^ (s τ)) *
      Formalism.L2.Forms.subP (fun τ => (M : Matrix (Fin n) (Fin n) D.host.E).map (embT D τ)) P := by
  rfl

theorem twSub_mem_ratSpan : ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ),
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → twSub (embT D) M s P0 ∈ Formalism.L2.Forms.RatSpan D lam := by
  classical
  intro D n lam M s P0 hP
  let A : Matrix (Fin n) (Fin n) D.host.E := (M : Matrix (Fin n) (Fin n) D.host.E)
  let ML : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL := fun τ => A.map (Formalism.L2.G.Cmp.tEL D τ)
  have hoM : ∀ τ, A.map (embT D τ) = (ML τ).map D.what₂.embLL := fun τ => by
    ext a b
    exact (Formalism.L2.G.Cmp.tEL_emb D τ _).symm
  have hdetA : A.det ≠ 0 := (Matrix.isUnits_det_units M).ne_zero
  have hMdet : ∀ τ, (ML τ).det ≠ 0 := by
    intro τ h
    apply hdetA
    have : Formalism.L2.G.Cmp.tEL D τ A.det = 0 := by
      rw [RingHom.map_det]; exact h
    exact (map_eq_zero _).1 this
  have hc : (∏ τ, (embT D τ A.det) ^ (s τ)) =
      D.what₂.embLL (∏ τ, (ML τ).det ^ s τ) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply, hoM τ, RingHom.map_det D.what₂.embLL, RingHom.mapMatrix_apply]
  rw [twSub_eq_subP]
  show C (∏ τ, (embT D τ A.det) ^ (s τ)) * Formalism.L2.Forms.subP (fun τ => A.map (embT D τ)) P0 ∈ _
  rw [hc, MvPolynomial.C_mul']
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hf, rfl⟩ := hp
    rw [map_smul, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.substitution_tensor, smul_smul, ← map_mul]
    apply Formalism.L2.GlobalTheoryTheory.LemB.rat_ten D _ Finset.univ
    · intro τ _
      rw [hoM τ]
      exact Formalism.L2.GlobalTheoryTheory.LemB.rat_rowAct_mem D _ (Formalism.L2.DIV.natW_antitone _) (ML τ) (hMdet τ) _
        (Submodule.subset_span ⟨f τ, hf τ, rfl⟩)
    · intro τ hτ
      exact absurd (Finset.mem_univ τ) hτ
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

end GlobalTheory.IntegralityCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedSourceValueReadInChangedBases
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.Mem.SrcFunRead

open MvPolynomial

theorem map_twSubK_field {E K K' ι : Type} [Field E] [Field K] [Field K'] [Fintype ι] {n : ℕ} (t : ι → E →+* K)
    (M : GL (Fin n) E) (s : ι → ℤ) (P : MvPolynomial (ι × Fin n × Fin n) K) (φ : K →+* K') :
    map φ (twSubK t M s P) = twSubK (fun τ => φ.comp (t τ)) M s (map φ P) := by
  simp only [twSubK, map_mul, map_C, map_prod, map_zpow₀, RingHom.comp_apply]
  congr 1
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp]

theorem eq_of_eval_invertible {LL ι : Type} [Field LL] [Fintype ι] {n : ℕ} (e : LL →+* ℂ)
    {A B : MvPolynomial (ι × Fin n × Fin n) LL}
    (h : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ).det ≠ 0) →
      eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (map e A) =
        eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (map e B)) : A = B := by
  classical
  let d : MvPolynomial (ι × Fin n × Fin n) ℂ :=
    ∏ τ, (Matrix.of fun a b : Fin n => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det
  have hd : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ,
      eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) d = ∏ τ, (y τ).det := by
    intro y
    simp only [d, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp
  have hd0 : d ≠ 0 := by
    intro h0
    have h1 := hd (fun _ => 1)
    rw [h0] at h1
    simp at h1
  have hm : d * map e A = d * map e B := by
    apply MvPolynomial.funext
    intro x
    obtain ⟨y, rfl⟩ : ∃ y : ι → Matrix (Fin n) (Fin n) ℂ, x = fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2 :=
      ⟨fun τ a b => x (τ, a, b), rfl⟩
    rw [eval_mul, eval_mul, hd]
    by_cases hy : ∀ τ, (y τ).det ≠ 0
    · rw [h _ hy]
    · push_neg at hy
      obtain ⟨τ, hτ⟩ := hy
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, zero_mul, zero_mul]
  exact MvPolynomial.map_injective e e.injective (mul_left_cancel₀ hd0 hm)

end GlobalTheory.Mem.SrcFunRead

namespace GlobalTheory.Mem.SrcFunRead
open MvPolynomial

theorem srcFun_secC_read : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z))
    (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs →
    (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) →
    ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m)
    (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY →
    ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ)
    (P0 : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N i) × Fin ((I.rec7 l Z).R.N i)) ℂ),
    (∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P0 (eY z)) →
    ∀ (R0 : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N i) × Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL),
    MvPolynomial.map (I.rec7 l Z).what₂.embLL R0 = P0 →
    ∀ (k : (I.rec7 l Z).what₂.Tau → ℕ),
    (∀ τ, (k τ : ℤ) = shiftOf (lamTG (I.fm l u μ) i) τ + ((I.rec7 l Z).chTw u μ).sSharp i τ) →
    ∀ (Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)
    (g : (I.rec7 l Z).what₂.Tau → Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) ℂ_[(I.rec7 l Z).what₂.places.resChar w]),
    (∀ τ, Bs u μ w i c τ = (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ) * g τ) →
    ∀ v : ValQ O u μ i, evC O u μ i v = f →
    srcFun Pl Bs u μ w i c (secC O u μ i v) = fun y =>
      (∏ τ, (g τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) * ((∏ τ, (g τ * y τ).det ^ k τ) *
        polFun (MvPolynomial.map (Pl.iL w) (twSubK (Formalism.L2.G.Cmp.tEL (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) R0))
          (fun τ => g τ * y τ)) := by
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hId c f P0 hf R0 hR0 k hk Bm g hBs v hv

  have hPI : (secC O u μ i v : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL) *
      ∏ τ, frDet (I.rec7 l Z).what₂.LL ((I.rec7 l Z).R.N i) τ ^ (((I.rec7 l Z).chTw u μ).sSharp i τ - twB (I.rec7 l Z) u μ i τ).toNat =
      R0 * ∏ τ, frDet (I.rec7 l Z).what₂.LL ((I.rec7 l Z).R.N i) τ ^ k τ := by
    apply eq_of_eval_invertible (I.rec7 l Z).what₂.embLL
    intro y hy
    obtain ⟨z, hz⟩ : ∃ z : (I.chain l u μ).Y i, z.1 = y := by
      refine ⟨eY.symm ⟨y, fun τ => isUnit_iff_ne_zero.2 (hy τ)⟩, ?_⟩
      have h2 := hId (eY.symm ⟨y, fun τ => isUnit_iff_ne_zero.2 (hy τ)⟩)
      exact h2.symm.trans (congrArg Subtype.val (eY.apply_symm_apply _))
    have h1 : evP O u μ i (secC O u μ i v) z = f z :=
      (congrFun (evC_sec O u μ i v) z).symm.trans (congrFun hv z)
    rw [hf z] at h1
    have hfr : (O u μ).frm i z = y := (hStd.frm u μ i z).trans hz
    have hde : ∀ τ, ((I.rec7 l Z).chTw u μ).de i z τ = (y τ).det := fun τ =>
      ((O u μ).frm_de i hi.le z τ).trans (congrArg (fun M => (M τ).det) hfr)
    have hez : (eY z).1 = y := (hId z).trans hz
    simp only [evP, LinearMap.coe_mk, AddHom.coe_mk, fnOf, GL3Theta.evFr, hfr, hde, hez, Matrix.one_mul, Pi.one_apply] at h1
    rw [← hR0] at h1
    simp only [map_mul, map_prod, map_pow, eval_mul, eval_prod, eval_pow, eval_detP (D := I.rec7 l Z)]
    have e1 : ∀ τ, (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ - twB (I.rec7 l Z) u μ i τ).toNat =
        (y τ).det ^ (-twB (I.rec7 l Z) u μ i τ) * (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ) := by
      intro τ
      rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.2 (twLe (I.rec7 l Z) u μ i hi τ)), ← zpow_add₀ (hy τ)]
      congr 1
      ring
    have e2 : ∀ τ, (y τ).det ^ k τ =
        (y τ).det ^ shiftOf (lamTG (I.fm l u μ) i) τ * (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ) := by
      intro τ
      rw [← zpow_natCast, hk τ, zpow_add₀ (hy τ)]
    simp only [e1, e2, Finset.prod_mul_distrib]
    linear_combination (∏ τ, (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ)) * h1
  funext y
  simp only [srcFun, atBas, LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.mulRight_apply, Submodule.coe_subtype, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [hPI]
  have hφ : ∀ τ x, ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) x = TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ x := by
    intro τ x
    have hx : (I.rec7 l Z).what₂.embLL (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ x) ∈ algebraicClosure ℚ ℂ := embLL_alg w _
    have he := Formalism.L2.G.Cmp.tEL_emb (I.rec7 l Z) τ x
    rw [RingHom.comp_apply, Pl.iL_lam' w _ hx]
    unfold TaylorLogMetric.tauEmb TaylorLogMetric.lamC
    rw [dite_eq_left (he ▸ hx)]
    exact congrArg (Pl.lam w) (Subtype.ext he)
  have hA : ∀ τ, (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
      (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ) =
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
      ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) := fun τ => by
    ext a b
    exact (hφ τ _).symm
  have hdetA : ∀ τ, ((Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
      ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))).det =
      ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det :=
    fun τ => (RingHom.map_det _ _).symm
  have ha : ∀ τ, ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det ≠ 0 :=
    fun τ => ((Matrix.isUnits_det_units Bm).map _).ne_zero
  simp only [hBs, hA]
  rw [map_twSubK_field, polFun_apply, eval_twSubK _ _ _ _ (fun τ => g τ * y τ)]
  simp only [map_mul, map_prod, map_pow, eval_mul, eval_prod, eval_pow, eval_detP (D := I.rec7 l Z),
    Matrix.mul_assoc, Matrix.det_mul, hdetA]
  have hev : ∀ τ, eval (fun k : GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i) =>
      ((Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) k.1)) * (g k.1 * y k.1)) k.2.1 k.2.2)
      (MvPolynomial.map (Pl.iL w) (frDet (I.rec7 l Z).what₂.LL ((I.rec7 l Z).R.N i) τ)) =
      ((Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) * (g τ * y τ)).det :=
    fun τ => eval_detP (D := I.rec7 l Z) (Pl.iL w) (fun t =>
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) t)) * (g t * y t)) τ
  simp only [hev, Matrix.det_mul, hdetA]
  have hper : ∀ τ, (((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
        (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det * (g τ).det) ^
          (-((I.rec7 l Z).chTw u μ).sSharp i τ) *
      (((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
        (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det *
          ((g τ).det * (y τ).det)) ^ k τ =
      ((g τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ) * ((g τ).det * (y τ).det) ^ k τ) *
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
          (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det ^
            shiftOf (lamTG (I.fm l u μ) i) τ := by
    intro τ
    have h0 := ha τ
    rw [mul_zpow, mul_pow, ← zpow_natCast (((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det), hk τ,
      zpow_add₀ h0, _root_.zpow_neg]
    have h1 : ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det ^
        (((I.rec7 l Z).chTw u μ).sSharp i τ) ≠ 0 := zpow_ne_zero _ h0
    field_simp
  rw [mul_left_comm, ← mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun τ _ => hper τ,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end GlobalTheory.Mem.SrcFunRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitCOfCXiAt
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.OneMapTuples.unitC_of_cXiAt : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (V : HSp D) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n r : ℕ) (d : DeltaDat Xo c n) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → ∀ (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → ReciprocityTheory.ChartRestriction.G.FD.gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → d.IsLev → d.l₂.A = 1 → ∀ (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (N : ℕ), 0 < N → (∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V h)) ^ N = 1) → ∀ (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (U₂.X k).Ψ r) (c0 : ℂ), c0 ^ N = 1 → GlobalTheory.OneMapAll.CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0 → GlobalTheory.Dict.UnitC d := by
  intro D H Dw V l Xo c n r d hr io hι hpq x₀ hx₀ hd hA xi N hN hxN U dict c0 hc0 hv A y
  subst hr
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  obtain ⟨-, -, -, -, -, -, -, hsec, -⟩ := hd
  have hc0' : c0 ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hc0; exact zero_ne_one hc0
  have hσ : GoodEmb d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) := rfl
  have val₀ : ∀ h : GA D V, ∃ hx : (dict h).2 ∈ (U.X (dict h).1).dom,
      toC (evR d.Xo₂ d.c₂ d.cδ (U.un _ ⟨_, hx⟩)) ^ N = 1 := by
    intro h
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    have hv := hval h γ ⟨hγ, hΛ, hm⟩
    obtain ⟨hx, ex⟩ := GlobalTheory.ShortMove.rdU_eq U d.cδ _ _ (hv ▸ mul_ne_zero hc0' (Units.ne_zero _))
    refine ⟨hx, ?_⟩
    rw [ex.symm.trans hv, mul_pow, hc0, ← Units.val_pow_eq_pow_val, hxN, Units.val_one, one_mul]
  choose hdom val₀ using val₀
  have hx : ∀ k, IsOrthogonalFrame (U.X k) x₀ := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx₀ τ (((hU.2.1 k).2 τ).1 hτ)
  have hroot : ∀ z : FrPt d.Xo₂ d.c₂ (CAt (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F))),
      evR d.Xo₂ d.c₂ d.cδ z ^ N = 1 := fun z => by
    obtain ⟨h, hh⟩ := GlobalTheory.TwistTie.exists_dict_over V U dict io e₀ F ik φ th x₀ hσ hA hpq hU hW hD hι hth hx hdom z
    rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hsec hh]
    exact val₀ h
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have h1 := GlobalTheory.FiniteOrderRule.pow_eq_one_of_complex (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) (GlobalTheory.Frames.algebraic_laws hS _ H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS _ H Dw d.l₂ d.Xo₂ d.c₂ S T φ y)
    _ d.cδ hsec.1 N hroot
  have h3 := @GlobalTheory.FiniteOrderRule.evalAt_pow_eq_one d.c₂.F _ (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) d.cδ N h1 ℂ _ A y
    (@GlobalTheory.Frames.allTest_of_secBaseChange hS _ _ _ _ H Dw d.l₂ d.Xo₂ d.c₂ ℂ _ inferInstance A y)
  exact Complex.norm_eq_one_of_pow_eq_one h3 hN.ne'

end
end

