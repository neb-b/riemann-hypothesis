module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateModelSameThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AMiEqAMinusQ
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RecordWeightVec

theorem aPl_eq_aPlusQ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) τ n : ℚ) = DV.aPlusQ D ((i : ℕ) + 1) τ n := by
  have hi := i.2
  have h1 : DV.sigPar D τ n = Formalism.L2.NTheta.lamAt (D.hc τ) n := by
    unfold DV.sigPar Formalism.L2.NTheta.lamAt
    rfl
  have h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i := by
    unfold DV.eQ
    rw [dite_eq_left ⟨by omega, by omega⟩]
    rfl
  rw [GlobalTheory.CoefMapRecord.aPl_cast D i τ n hn, DV.aPlusQ_eq, h1, h2]
  push_cast
  ring

theorem aMi_eq_aMinusQ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (q n c : ℕ) (hq : i + 1 + q = D.R.m)
    (hn : n + c + 1 = q) : (aMi D i (D.R.k + i) q τ n : ℚ) = DV.aMinusQ D ((i : ℕ) + 1) τ c := by
  have hi := i.2
  have h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i := by
    unfold DV.eQ
    rw [dite_eq_left ⟨by omega, by omega⟩]
    rfl
  rw [GlobalTheory.CoefMapRecord.aMi_cast D i τ q n c hq hn, DV.aMinusQ, dite_eq_left (by omega), h2]
  ring

theorem wtOf_kapTop : ∀ D : D7, DV.KapDef D → ∀ i : Fin D.R.m,
    (kapTop D i).n = D.R.nV ∧ Formalism.L2.Geo.wtOf (kapTop D i) = DV.kapW D ((i : ℕ) + 1) := by
  intro D hK i
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have hs : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ =>
    D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by
    simp only [Ranks.sigW]; omega
  have hq : i + 1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m := by
    simp only [Ranks.sigW]; omega
  refine ⟨rfl, Formalism.L2.Geo.wtOf_eq_kapW _ (fun τ a => ?_) (fun τ c => ?_) rfl⟩
  · have h := (hK _ (inR i).1 (inR i).2 τ).1 a
    have h' := aPl_eq_aPlusQ D i τ a (hp ▸ a.2)
    have he := (kapIs_kapTop D i τ).1 a
    rw [he, hs τ]
    rw [← h, ← hp] at h'
    exact_mod_cast h'
  · have h := (hK _ (inR i).1 (inR i).2 τ).2 (Fin.rev c)
    have hc := c.2
    have h' := aMi_eq_aMinusQ D i τ _ c (Fin.rev c) hq (by rw [Fin.val_rev]; omega)
    have he := (kapIs_kapTop D i τ).2.1 c
    rw [he, hs τ]
    rw [← hp, ← neg_neg (DV.aMinusQ _ _ _ _), ← h] at h'
    exact_mod_cast h'

end GlobalTheory.RecordWeightVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicThetaOfTestFunctionExistsLawsFockVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem pureTensorL_rename {ι κ X : Type} {A : κ → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f)) {f : X → ℂ} (hf : P f)
    (e : ι → κ) (Q : MvPolynomial ι ℂ) :
    pureTensorL (fun i => A (e i)) f Q = pureTensorL A f (MvPolynomial.rename e Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [MvPolynomial.rename_monomial, Ker.FockAlg.pure_monomial, Ker.FockAlg.pure_monomial]
    congr 1
    unfold opPow
    rw [← List.foldr_map (f := e) (g := fun i g => A i g)]
    refine Ker.FockAlg.foldr_perm hA hc hf ?_
    rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
      Finsupp.toMultiset_map]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

theorem unitMap_perm {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin m) (Fin m) ℂ) (π : Equiv.Perm (Fin m))
    (a : Fin m) (k : Fin n) : unitMap B (Z.submatrix id π) (π.symm a) k = unitMap B Z a k := by
  unfold unitMap
  congr 1
  ext i j
  by_cases h : j = k
  · subst h
    simp
  · simp [h]

theorem fvec_perm {D : D7} {S T : HSp D} (C : Ker.Ctx S T) (Z : Fam T) (π : Equiv.Perm (Fin T.rank))
    (hB : C.IsB fun ρ => (Z ρ).submatrix id π) {f : WO S T → ℂ} (hf : C.IsTh f)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB fun ρ => (Z ρ).submatrix id π) (fun _ => 1) Z f Q =
      C.fvec (fun ρ => (Z ρ).submatrix id π) f (MvPolynomial.rename (fun v => (v.1, π.symm v.2.1, v.2.2)) Q) := by
  have h := pureTensorL_rename (P := C.IsTh)
    (A := aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB (fun ρ => (Z ρ).submatrix id π) τ)) (fun _ => 1)
      (fun ρ => (Z ρ).submatrix id π))
    (fun _ _ h => Ker.FockAlg.aPlus_th C _ _ _ h)
    (fun i j _ h => Ker.FockAlg.aPlus_comm C i.1 _ hB j.1 _ h) hf
    (fun v : FVar D T.rank S.rank => (v.1, π.symm v.2.1, v.2.2)) Q
  refine Eq.trans ?_ h
  unfold pureTensorO
  congr 2
  funext i
  simp only [aPlusAll, unitMap_perm]

theorem zak_laws : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ Z : Fam T, IsONeg T X.p0 Z → (∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → (∃ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f) ∧ ∀ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f → (∀ f', Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f' → f' = f) ∧ (∀ φ', GlobalTheory.SW.IsSB φ' → Zak ψ θ hr eT bas idx (frOf hr eT Z) φ' f → φ' = φ) ∧ (∀ a : ℂ, Zak ψ θ hr eT bas idx (frOf hr eT Z) (a • φ) (a • f)) ∧ (∀ φ' f', GlobalTheory.SW.IsSB φ' → Zak ψ θ hr eT bas idx (frOf hr eT Z) φ' f' → Zak ψ θ hr eT bas idx (frOf hr eT Z) (φ + φ') (f + f')) ∧ (∀ y : Matrix (Fin S.rank) (Fin r) D.host.E, Zak ψ θ hr eT bas idx (frOf hr eT Z) (heisG X bas (-y) φ) (heisO ψ S T (finR S hr y) f)) ∧ (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO 1 (cartZ T X.p0 Z ρ)) f) ∧ ∀ (q0 : ℕ) (hq : X.p0 + q0 = r) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), fv ψ θ S T X.p0 Z f Q 0 = thP X hq bas idx φ (toP S hr eT hq Q) (frOf hr eT Z)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO 1 (cartZ T X.p0 Z ρ)) f) → ∃ φ : TF S.rank g, GlobalTheory.SW.IsSB φ ∧ Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f := by
  intro D S T r g hr ψ θ X eT bas idx hS Z hZ
  have hq0 : X.p0 + (r - X.p0) = r := Nat.add_sub_cancel' X.p0_le
  obtain ⟨X', m, hq', bas', idx', hs, π, -, -, hheis, hZZ⟩ :=
    _root_.GlobalTheory.OneMapRef.Flip.exists_flip_model D S T r g hr ψ θ X eT bas idx hS (r - X.p0) hq0
  obtain ⟨hB, hrest⟩ := hZZ Z
  obtain ⟨hsB, hzak, hthP⟩ := hrest hZ
  have hB := hB.1 hZ
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC
  set B : C.Bas := fun ρ => (Z ρ).submatrix id π with hBdef
  have hx : C.xB B ∈ C.X.dom := ((_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.1
  have key : ∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → ∀ f,
      Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f ↔ f = C.Th (C.xB B) φ := by
    intro φ hφ f
    rw [← hzak]
    exact ⟨(_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hx φ hφ).2 f, fun h => h ▸ (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hx φ hφ).1⟩
  refine ⟨fun φ hφ => ⟨⟨_, (key φ hφ _).2 rfl⟩, fun f hf => ?_⟩, fun f hf hF => ?_⟩
  · have hth : C.IsTh f := hf.1
    obtain rfl := (key φ hφ f).1 hf
    obtain ⟨l1, l2, l3, -⟩ := _root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hx φ hφ
    obtain ⟨f1, f2⟩ := (_root_.GlobalTheory.Ker.fvec_Th_zero D S T C).2 B hB φ hφ
    refine ⟨fun f' hf' => (key φ hφ f').1 hf', fun φ' hφ' h => ?_, fun a => ?_, fun φ' f' hφ' h => ?_,
      fun y => ?_, fun ρ => ?_, fun q0 hq Q => ?_⟩
    · exact ((l1 φ' hφ').2 ((key φ' hφ' _).1 h)).symm
    · exact (key _ ((GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ hφ hφ).2.1 a) _).2 (l2 a).symm
    · rw [(key φ' hφ' _).1 h]
      exact (key _ (GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ' hφ hφ').1 _).2 (l1 φ' hφ').1.symm
    · refine (key _ ((heisG_laws _ r X g bas idx S.rank hS.2.2.2.2.2.2.2 hS.2.2.2.1).2.2.2 (-y) φ hφ).1 _).2 ?_
      rw [← hheis]
      exact l3 _
    · rw [← hsB]
      exact f1 ρ
    · obtain rfl : q0 = r - X.p0 := by omega
      rw [← hthP, fv, ← hsB]
      exact (congrFun (fvec_perm C Z π hB hth Q) 0).trans (f2 _)
  · obtain ⟨φ, ⟨hφ, h⟩, -⟩ := (Ker.th_bij_fock D S T C B hB).2 f hf (fun ρ => by rw [hsB]; exact hF ρ)
    exact ⟨φ, hφ, (key φ hφ f).2 h⟩

end GlobalTheory.OneMapRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOfSmoothCuspidalUniformModerate
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.CuspDecay

theorem bounded_of_smooth_unifModGrowth : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ φ : GA D V → ℂ, IsAutFun V φ → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn V θ φ → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsUnifModGrowth V θ φ → IsCuspFun V φ → ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  intro hP D θ V hθ φ ha hs hg hc
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hs' := (GlobalTheory.SmoothForms.smooth_iff R φ).1 hs
  exact (hP D θ hθ V _ (GlobalTheory.SmoothForms.isExpFam_expInf R) φ ha hs'
    ((GlobalTheory.SmoothForms.growth_iff hθ R ha hs').1 hg) hc).bounded

end GlobalTheory.CuspDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClsAt
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtId

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}

def ClsAt {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (δ : ℤˣ) : Prop :=
  ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (g q0 : ℕ) (X : Data D.host.E D.R.r) (hq : X.p0 + q0 = D.R.r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (x₀ : Frame X.Ψ D.R.r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), IsMod (Wc D i) (rank_Wc i) X → IsSympl X bas → IsONFr X x₀ → IsInvOf (Wc D i) (rank_Wc i) X x₀ (cart (R.MW i (sg0 D A))) → IsBasOf (Wc D i) (rank_Wc i) X hq x₀ (onb (R.MW i (sg0 D A))) → IsVarOf (Vc D i) (Wc D i) X q0 vr → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC (Vc D i) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → ∀ (v : TF (Vc D i).rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) (latR (rank_Wc i) (latG (Wc D i) k))) v → Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) X bas idx (R.ωP i t (1, k) (R.vacP i)) (a • v) (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) → ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin (Vc D i).rank)) (d : ℕ), P.IsHomogeneous d → thetaKO (R.ωP i t) h k (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename vr P)) = ((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * ((((Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR (rank_Wc i) (latG (Wc D i) k)) v (hatC l₂ φ) Y) P (frMove R.θ (Wc D i) (rank_Wc i) X k x₀)

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def IoAt (O : OMDat T.toCore R i Tp tup) (v₀ : (R.MW i (sg0 D A)).Vec) (ka : ℂ) : Prop :=
  ∀ (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank), (∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ ρ) → ∀ (t : T0) (v : VsV D i O.c'.F), R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' v)) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename lt (MvPolynomial.map (inC O.c') (O.io v)))

def CovAt (O : OMDat T.toCore R i Tp tup) (c0 : ℂ) : Prop :=
  ∀ (t : Tp) (X : Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → IsSympl X bas → IdxIs O.c' (inC O.c') X idx e → latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → IsMark (O.dδ t).l₂ X.Λ mk → MarkAd (O.dδ t).l₂ (Wc D i) (rank_Wc i) (iotaW T i) k mk → letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra; ∀ (y₂ : FrPt (O.dδ t).Xo₂ (O.dδ t).c₂ ℂ) (A₂ : AnFib X bas idx e (frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.x₀ ((i : ℕ) + 1) O.s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (O.dδ t).Xo₂ (O.dδ t).c₂ (O.dδ t).cδ y₂ = c0 * ((R.xi (tup t) xk : Circle) : ℂ)

def degW {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ j : Fin (Dw.mult τ), a (τ, j)

end GlobalTheory.PtId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteUnitaryArchimedeanPointsDistinctPlacesStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ τ' : E →+* ℂ), InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → ∀ x ∈ embU n τ, ∀ y ∈ embU n τ', Commute x y := by
  first | exact @GlobalTheory.UnitaryBC.embU_commute | exact GlobalTheory.UnitaryBC.embU_commute | (intros; apply GlobalTheory.UnitaryBC.embU_commute <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMovPair
section
noncomputable section

open MeasureTheory
open scoped Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSupBound

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem continuous_mov_pair (hθ : IsInfFam θ) (u : RW T S) :
    Continuous fun p : GA D S × GA D T => mov θ p.1⁻¹ p.2⁻¹ u := by
  refine continuous_pi fun τ => ?_
  unfold mov
  simp only [inv_inv]
  exact (((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
    ((GlobalTheory.RealWeil.continuous_mt T).2.comp continuous_snd)).matrix_mul continuous_const).matrix_mul
    ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt S).1.comp continuous_fst))

theorem uniform_level_pair (hom : IsWeilDatumO ψ S T χS χT om) {U : AddSubgroup (WO S T)}
    (hU : IsOpen (U : Set (WO S T))) {C : Set (GA D S × GA D T)} (hC : IsCompact C) :
    ∃ K₀ ∈ 𝓝 (0 : WO S T), IsCompact K₀ ∧ ∀ p ∈ C, ∀ φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u φ = φ) → ∀ u ∈ K₀, u.map (infPart D) = 0 →
        heisO ψ S T u (om p φ) = om p φ := by
  obtain ⟨i1, i2, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hcont : Continuous fun z : WO S T × (GA D S × GA D T) => actO S T z.2.1⁻¹ z.2.2⁻¹ z.1 := by
    unfold actO
    simp only [inv_inv]
    exact (((GlobalTheory.RealWeil.continuous_mt T).2.comp (continuous_snd.comp continuous_snd)).matrix_mul
      continuous_fst).matrix_mul ((GlobalTheory.RealWeil.continuous_mt S).1.comp (continuous_fst.comp continuous_snd))
  have hev : ∀ᶠ u in 𝓝 (0 : WO S T), ∀ p ∈ C, actO S T p.1⁻¹ p.2⁻¹ u ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun p _ => ?_
    refine hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds ?_)
    show actO S T p.1⁻¹ p.2⁻¹ 0 ∈ U
    unfold actO
    rw [Matrix.mul_zero, Matrix.zero_mul]
    exact U.zero_mem
  obtain ⟨K₀, h0, hsub, hK₀⟩ := LocallyCompactSpace.local_compact_nhds (X := WA T S) 0 _ hev
  refine ⟨K₀, h0, hK₀, fun ⟨g, h⟩ hp φ hφ hl u hu hinf => ?_⟩
  have hv : (actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hinf, Matrix.mul_zero, Matrix.zero_mul]
  have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ u) φ hφ
  rw [hl _ (hsub hu _ hp) hv, actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
  exact e.symm

theorem cube_bound_at (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) {N : ℕ}
    (b : Module.Basis (Fin N) ℝ (RW T S)) {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T)) (hK₀ : IsCompact K₀) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ p φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T u (om p φ) = om p φ) → ∀ B : ℝ, (∀ w, ‖φ w‖ ≤ B) → ∀ y,
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1),
        ‖om p φ (y + ∑ i, iotaW σ T S (t i • b i))‖ ^ 2 ≤ c * B ^ 2 := by
  obtain ⟨c, hc0, hcube⟩ := cube_bound hom hc b h0 hK₀
  refine ⟨c, hc0, fun ⟨g, h⟩ φ hφ hl B hB y => ?_⟩
  have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ y) φ hφ
  rw [actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
  have hn := GlobalTheory.HeisOrtho.norm_heisO (S := S) (T := T) hom.std.1
  have key := hcube (g, h) _ (GlobalTheory.ThetaClosed.thetaClosed ψ θ hom.std hc.inf S T φ hφ |>.1 (actO S T g⁻¹ h⁻¹ y))
    (fun w hw => by
      generalize hu : w - iotaW σ T S (piW θ T S w) = u at hw
      have hinf : u.map (infPart D) = 0 := by
        have hp : piW θ T S u = 0 := by
          rw [← hu, AddMonoidHom.map_sub, hc.pi_iota, sub_self]
        ext i j
        exact ThetaCont.infPart_eq_zero hc _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
      rw [e, hn, hn]
      conv_rhs => rw [← hl u hw hinf, hn, ← hu]
      congr 2
      abel_nf) B (fun w => by rw [hn]; exact hB _)
  simp only [e, hn, zero_add] at key
  simpa only [add_comm y] using key

theorem exists_sup_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ C : Set (GA D S × GA D T), IsCompact C →
      ∃ c : ℝ, ∀ p ∈ C, ∀ w, ‖om p f w‖ ≤ c := by
  intro D ψ S T χS χT om hom f hf C hC
  have hψ := hom.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have b := Module.finBasis ℝ (RW T S)
  generalize Module.finrank ℝ (RW T S) = N at b
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K₀, h0, hK₀, hlev⟩ := uniform_level_pair hom hU hC
  obtain ⟨c, hc0, hcube⟩ := cube_bound_at hom hc b h0 hK₀
  obtain ⟨C₁, hC₁0, hC₁⟩ := words_bound (dvL hc hψ S T) (fun w => (LinearMap.proj w).comp (thetaSub ψ S T).subtype)
    (fun (m : thetaSub ψ S T) => theta_bounded hψ m.2) N ⟨f, hf⟩
  obtain ⟨κ, hκ⟩ := hC.exists_bound_of_continuousOn
    (f := fun (p : GA D S × GA D T) (i : Fin N) => mov θ p.1⁻¹ p.2⁻¹ (b i))
    (continuous_pi fun i => continuous_mov_pair hθ (b i)).continuousOn
  refine ⟨√(4 ^ N * (c * (C₁ * max 1 κ ^ N) ^ 2)), fun ⟨g, h⟩ hp w => ?_⟩
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ max 1 κ) ∧ F = om (g, h) (wd l).1}
  refine Real.le_sqrt_of_sq_le (sobolev_iter N 0 (fun i r => iotaW σ T S (r • b i)) A (c * (C₁ * max 1 κ ^ N) ^ 2) w
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ (om (g, h) f) ⟨[], le_rfl, by simp, rfl⟩)
  · rintro p _ ⟨l, h1, h2, rfl⟩
    have hF := hom.om_pres (g, h) _ (wd l).2
    refine ⟨hF.cont, fun i => ⟨_, ⟨l ++ [mov θ g⁻¹ h⁻¹ (b i)], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (b i) hF⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        exact ((norm_le_pi_norm (fun i => mov θ g⁻¹ h⁻¹ (b i)) i).trans (hκ (g, h) hp)).trans (le_max_right _ _)
    · rw [dv_om hom hc g h (b i) (wd l).2]
      simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    exact hcube (g, h) _ (wd l).2 (hlev (g, h) hp _ (wd l).2 fun u hu h0 => words_level hc hψ h0 l _ (hl u hu h0)) _
      (hC₁ _ (le_max_left _ _) l (by simpa using h1) h2) w

end GlobalTheory.WeilSupBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

variable {D : D7} {θ : InfF D} {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem exp_mem (hX : X ∈ lieAt V τ) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
  GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t

theorem isAtTau_oneP (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (t : ℝ) :
    IsAtTau θ V τ (NormedSpace.exp (t • X)) (oneP θ V τ X t) :=
  GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (exp_mem hX t)

theorem oneP_add (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (s t : ℝ) :
    oneP θ V τ X (s + t) = oneP θ V τ X s * oneP θ V τ X t := by
  unfold oneP
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (exp_mem hX s) (exp_mem hX t), add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]

theorem oneP_zero (hθ : IsInfFam θ) : oneP θ V τ X 0 = 1 := by
  unfold oneP
  rw [zero_smul, NormedSpace.exp_zero, GlobalTheory.PointAtPlaceHom.atTau_one hθ]

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Matrix (Fin n) (Fin n) ℂ) i j)
      ((NormedSpace.exp (t • X) * X : Matrix (Fin n) (Fin n) ℂ) i j) t := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt.comp_hasDerivAt t h

end

theorem continuous_oneP (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) : Continuous (oneP θ V τ X) :=
  (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous
    (continuous_matrix fun i j => continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_entry X t i j).continuousAt)
    (exp_mem hX)

theorem hasDerivAt_oneP (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {φ φ' : GA D V → ℂ}
    (h : ∀ g, HasDerivAt (fun t : ℝ => φ (g * oneP θ V τ X t)) (φ' g) 0) (g : GA D V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (g * oneP θ V τ X s)) (φ' (g * oneP θ V τ X t)) t := by
  have h1 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h (g * oneP θ V τ X t))
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [mul_assoc, ← oneP_add hθ hX, add_sub_cancel]

theorem hasDerivAt_Rder {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hX : X ∈ lieAt V τ) (g : GA D V) :
    HasDerivAt (fun t : ℝ => φ (g * oneP θ V τ X t)) (Rder θ V τ X φ g) 0 :=
  (differentiable_oneP hφ hX g 0).hasDerivAt


attribute [local instance 100] LieRing.ofAssociativeRing in
theorem glRel_derEnd (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : Formalism.REAL.GlRel fun a b : Fin V.rank =>
    GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (Matrix.single a b 1) := by
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  obtain ⟨P, Q, hPQ, h⟩ := _root_.GlobalTheory.UnitaryLieComplexification.glRel_and_span _ _ (R.1 τ).1 (R.1 τ).2
  have hG := (h _ (fun X => GlobalTheory.SmoothForms.opInf R (atPlace V τ X)) (GlobalTheory.SmoothForms.opAt_add R τ)
    (GlobalTheory.SmoothForms.opAt_smul R τ) (GlobalTheory.SmoothForms.opAt_bracket R τ)).1
  have e : SmFun θ V = GlobalTheory.SmoothForms.SmF θ V := Submodule.ext fun φ => GlobalTheory.SmoothForms.smooth_iff R φ
  let E := (LinearEquiv.ofEq _ _ e).conjAlgEquiv ℂ
  have k : ∀ a b, E (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (Matrix.single a b 1)) =
      GlobalTheory.SmoothForms.opInf R (atPlace V τ (P a b)) + Complex.I • GlobalTheory.SmoothForms.opInf R (atPlace V τ (Q a b)) := by
    intro a b
    refine LinearMap.ext fun φ => Subtype.ext ?_
    change RderC θ V τ (Matrix.single a b 1) φ.1 = _
    rw [RderC, conjAt, ← (hPQ _ _).1, ← (hPQ _ _).2, GlobalTheory.SmoothForms.Rder_eq R, GlobalTheory.SmoothForms.Rder_eq R]
    rfl
  intro a b c d
  apply E.injective
  have := hG a b c d
  simp only [← k] at this
  simp only [map_sub, map_mul, this, apply_ite E, map_zero]

end GlobalTheory.Mem.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFiniteStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_classSet_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ x ∈ infU E n, ∃ k ∈ K, g = γ * s * x * (k : UA E n) := by
  first | exact @GlobalTheory.DefU.ClassFin.classSet_finite | exact GlobalTheory.DefU.ClassFin.classSet_finite | (intros; apply GlobalTheory.DefU.ClassFin.classSet_finite <;> assumption)
end

