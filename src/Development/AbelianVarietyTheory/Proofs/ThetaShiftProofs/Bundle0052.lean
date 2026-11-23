module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobi
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0036
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.IntModelExists

theorem dualMap_id (R : Type) [CommRing R] : dualMap (RingHom.id R) = RingHom.id _ :=
  by
    apply RingHom.ext
    intro x
    ext <;> simp [dualMap]

theorem maps_self {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) {w : LB.Iso L (L.pull F)}
    (hw : w = isoPullId (idIso L) hF) {h : Y ⟶ Y} (hh : h = 𝟙 Y) {K I : Type} [Fintype K] (φ : I → K → (Y ⟶ X))
    (ε : K → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) ε)) (ht : ∀ i, (t i).IsGen) {i i' : I} (hi : i' = i) :
    ∃ hψ : ∀ k, φ i k ≫ F = h ≫ φ i' k,
      LB.Gen.Maps (LB.linCombIso w _ ε) (t i) (Out.GeneratorPullback.pullAlong L F h _ ε _ hψ (t i')) := by
  subst hi hw hh
  have hψ : ∀ k, φ i' k ≫ F = 𝟙 Y ≫ φ i' k := fun k => by rw [hF, Category.comp_id, Category.id_comp]
  exact ⟨hψ, (maps_iff _ _ (φ i') ε (t i') (t i') (𝟙 Y) _ (Out.GeneratorPullback.pullAlong_le L F _ _ _ hψ) (fun _ => rfl)).2
    (NoTorus.pmaps_id hF _ _ (ht i'))⟩


open scoped CategoryTheory.Obj in
theorem exists_self {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) (h : ∀ χ, PsiUnitOn D χ Set.univ) :
    ∃ p : Out.IsPullDeg (RingHom.id R) D D, (∀ q : D.P.A.left ⟶ D.P.A.left, q ≫ prj p = prj p ≫ q) ∧
      (∀ y, p.xe y = y) ∧ ∀ ν, LetBC p ν ν := by
  have hgen {F : D.P.A.left ⟶ D.P.A.left} (hF : F = 𝟙 _) : PGen (isoPullId (Geo.Tor.idIso D.P.L) hF) := by
    subst F
    intro Y f y j j' k k' hj hj' hk hk'
    have hgw : ∀ a b, f y ∈ D.P.L.U a → f y ∈ D.P.L.U b →
        gw (isoPullId (Geo.Tor.idIso D.P.L) rfl) f y a b =
          gm f y _ (D.P.L.g a b) := by
      intro a b ha hb
      have hm : f y ∈ (D.P.L.pull (𝟙 _)).U (fun _ => a) ⊓ D.P.L.U b := ⟨mem_pull.2 ha, hb⟩
      exact gm_res f y _ hm _
    rw [hgw j k hj hk, hgw j' k' hj' hk', Category.comp_id]
    have hV : f y ∈ (D.P.L.U j ⊓ D.P.L.U k) ⊓ (D.P.L.U j' ⊓ D.P.L.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have hw' : res (inf_le_left : (D.P.L.U j ⊓ D.P.L.U k) ⊓ (D.P.L.U j' ⊓ D.P.L.U k') ≤ D.P.L.U j ⊓ D.P.L.U k) (D.P.L.g j k) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (D.P.L.U j ⊓ D.P.L.U k) ⊓ (D.P.L.U j' ⊓ D.P.L.U k') ≤ D.P.L.U j ⊓ D.P.L.U j') (D.P.L.g j j') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (D.P.L.U j ⊓ D.P.L.U k) ⊓ (D.P.L.U j' ⊓ D.P.L.U k') ≤ D.P.L.U k ⊓ D.P.L.U k') (D.P.L.g k k'))⁻¹ *
      res (inf_le_right : (D.P.L.U j ⊓ D.P.L.U k) ⊓ (D.P.L.U j' ⊓ D.P.L.U k') ≤ D.P.L.U j' ⊓ D.P.L.U k') (D.P.L.g j' k') :=
      (idIso_isGen D.P.isLB) (j, k) (j', k')
    have key := congrArg (gm f y ((D.P.L.U j ⊓ D.P.L.U k) ⊓ (D.P.L.U j' ⊓ D.P.L.U k'))) hw'
    simp only [map_mul, map_inv, gm_res f y _ hV] at key
    exact key
  have : IsMonHom (Iso.refl D.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.P.A))
  have gp : IsGrpPullback D.P.A D.P.A (Out.specOf (RingHom.id R)) (Iso.refl D.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (Out.specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.P.A.hom (Out.specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨ψW⟩ := GlobalTheory.ArcPull.nonempty_psiOn_top D h
  obtain ⟨p, h₁, h₂, h₃⟩ := UnifUniq.exists_isPullDeg_id D D ⊤ trivial ψW e me
    (isoPullId (idIso D.P.L) hF') ((isGen_iff _).2 (hgen hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (NoTorus.pmaps_id hF' (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => NoTorus.pmaps_id hF' (K := PUnit) (fun _ => D.xK x) (fun _ => -1) (D.psi_gen x))
  subst h₁
  have hx : ∀ y, p.xe y = y := fun y => by rw [h₃]; rfl
  have hp : prj p = 𝟙 _ := hF'
  have hs : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
    rw [dualMap_id]; exact Spec.map_id (CommRingCat.of (DualNumber R))
  refine ⟨p, fun q => by rw [hp, Category.comp_id, Category.id_comp], hx, fun ν => ⟨?_, fun χ => ?_⟩⟩
  · exact ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _)).trans
      ((congrArg (· ≫ ν.b.left) hs).trans (Category.id_comp _)).symm
  · exact maps_self hF' (eq_of_heq h₂) hs (Out.DegPre.gtφT D (epsR R) ν.b) _ ν.s ν.isGen (hx χ)

theorem isLieComb_trans {S : Type} [CommRing S] [IsLocalRing S] {G : Over (Sp S)} [GrpObj G] [Smooth G.hom] {d n : ℕ}
    {v : Fin d → (epsR S ⟶ G)} {u : Fin n → (epsR S ⟶ G)} {w : epsR S ⟶ G} (hv : ∀ i, IsTangent (v i))
    (hu : ∀ i, IsTangent (u i)) (hw : IsTangent w) {U : Fin n → Fin d → S} (hU : ∀ i, IsLieComb (U i) v (u i))
    {a : Fin n → S} (ha : IsLieComb a u w) : IsLieComb (fun j => ∑ i, a i * U i j) v w := by
  obtain ⟨m, y, hy⟩ := Chart.univChartLoc G
  have tv := fun i => (Chart.isTan_iff _).2 (hv i)
  have tu := fun i => (Chart.isTan_iff _).2 (hu i)
  have tw := (Chart.isTan_iff _).2 hw
  rw [Chart.comb_iff_coord hy _ tv tw, (Chart.comb_iff_coord hy _ tu tw).1 ha]
  simp only [(Chart.comb_iff_coord hy _ tv (tu _)).1 (hU _), Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem isLieComb_single {S : Type} [CommRing S] [IsLocalRing S] {G : Over (Sp S)} [GrpObj G] [Smooth G.hom] {d : ℕ}
    {v : Fin d → (epsR S ⟶ G)} (hv : ∀ i, IsTangent (v i)) (j : Fin d) : IsLieComb (Pi.single j 1) v (v j) := by
  obtain ⟨m, y, hy⟩ := Chart.univChartLoc G
  have tv := fun i => (Chart.isTan_iff _).2 (hv i)
  rw [Chart.comb_iff_coord hy _ tv (tv j)]
  simp [Pi.single_apply]

theorem flat_of_injective {A B : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f) : f.Flat := by
  algebraize [f]
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hf
  show Module.Flat A B
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_matrix (hG : Out.GlobalFnsSt) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e₁ e₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (h₁ : ArcBasis W ρ e₁) (h₂ : ArcBasis W ρ e₂) :
    ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A,
      (∀ τ, (g τ).det ≠ 0) ∧ ∀ τ k, GtComb (g τ k) (e₁ τ) (e₂ τ k) := by
  have key := (GlobalTheory.T.constantEigenbasis_independent_of_witness hG E H Dw l Xo c O β Y A b a χ W ρ e₁ h₁).2.2
  obtain ⟨v₁, i₁, b₁⟩ := h₁
  obtain ⟨v₂, i₂, b₂⟩ := h₂
  choose g hg using fun τ k => (key τ (e₂ τ k) (v₂ τ k)
    (((_root_.GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y A b a χ W (e₂ τ k)).2 _ (i₂ τ k)).2 ((b₂ τ).1 k).1) (i₂ τ k)
    ((b₂ τ).1 k).2).exists
  refine ⟨fun τ => Matrix.of (g τ), fun τ => ?_, hg⟩
  have := W.t.semi.smooth
  have hU : ∀ k, IsLieComb (fun i => PowerSeries.C (R := A) (g τ k i)) (v₁ τ) (v₂ τ k) := fun k =>
    (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W _ (g τ k) (e₁ τ) (e₂ τ k) (v₁ τ) (v₂ τ k) (i₁ τ) (hg τ k)).1 (i₂ τ k)
  choose h hh using fun j => ((b₂ τ).2 (v₁ τ j) ((b₁ τ).1 j).1 ((b₁ τ).1 j).2).exists
  have hm : Matrix.of h * (PowerSeries.C (R := A)).mapMatrix (Matrix.of (g τ)) = 1 := by
    ext1 j k
    have := congrFun (((b₁ τ).2 (v₁ τ j) ((b₁ τ).1 j).1 ((b₁ τ).1 j).2).unique
      (isLieComb_trans (fun i => ((b₁ τ).1 i).1) (fun i => ((b₂ τ).1 i).1) ((b₁ τ).1 j).1 hU (hh j))
      (isLieComb_single (fun i => ((b₁ τ).1 i).1) j)) k
    simpa [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  intro h0
  have := congrArg Matrix.det hm
  rw [Matrix.det_mul, ← RingHom.map_det, h0, map_zero, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem exists_arcBasis_baseChange (hL : Out.Laws) (hL₂ : Out.Laws2) (hU : Out.UnifBaseChangeSt) (hL₅ : Out.Laws5)
    {A A' : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A]
    [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsPrincipalIdealRing A'] {b : O →+* A} {b' : O →+* A'}
    {a : ArcIn Dw l β A b} {a' : ArcIn Dw l β A' b'} {f : A →+* A'} (hf : Function.Injective f)
    {p : Out.IsPullDeg f a.D₀ a'.D₀} (hp : InBC f a a' p) {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (h : ArcBasis W ρ e) :
    ∃ (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ))
      (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A')),
      (∀ τ k, LetBC p (e τ k) (e' τ k)) ∧ ArcBasis W' (fun τ => f.comp (ρ τ)) e' := by
  obtain ⟨hW, hν, -⟩ := (GlobalTheory.T.degenerationData_baseChanges_exist_pid hL hL₂ hU hL₅ E H Dw l Xo c O β Y A A' b a f hf b' hp.1).2 a' p hp
  obtain ⟨W', hW'⟩ := hW χ W
  choose e' he' using fun τ k => (hν (e τ k)).exists
  obtain ⟨m, -, hm, -⟩ := _root_.GlobalTheory.ArcBaseChange.main hL hL₂ E H Dw l Xo c O β Y A b a χ W A' b' a' f p W' hp hW'
  have hfl : ((PowerSeries.map f).comp (PowerSeries.C (R := A))).Flat := by
    refine flat_of_injective _ fun x y hxy => hf (PowerSeries.C_injective ?_)
    simpa using hxy
  open Matrix GlobalTheory.BasisUniv in
  have arcBasis_baseChange : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → ∀ (S : Type) [CommRing S] (ι : PowerSeries A →+* S), (ι.comp (PowerSeries.C (R := A))).Flat → ∀ (t' : SAB H (Sp S)) (m2 : SABMap t' W.t (spMap ι)), ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t'.G), (∀ τ k, ∃ v, LieImg W (e τ k) v ∧ (u τ k).left ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap ι) ≫ v.left) ∧ ∀ τ, (∀ k, IsTangent (u τ k) ∧ ∀ x : 𝓞 E, (u τ k ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ (u τ k).left) ∧ ∀ w : epsR S ⟶ t'.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left) → ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w := by
    intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ρ e hB S _ ι hflat t' m2
    obtain ⟨v₀, hv₀, hB⟩ := hB
    obtain ⟨g, e₁, v, M, hev, hv, hcomb, hM⟩ := GlobalTheory.T.exists_constantLieBasis_arcGroup hG E H Dw l Xo c O β Y A b a χ W
    have hsm : Smooth W.t.G.hom := W.t.semi.smooth
    have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
    have hmon' : ∀ x, IsMonHom (t'.act.act x) := t'.act.hom
    obtain ⟨n, y, hy⟩ := Chart.univChartLoc W.t.G
    obtain ⟨n', y', hy'⟩ := exists_chart_of_pullback ι m2.cart
  
    have hU : ∀ τ k, ∃ U : Fin g → A, IsLieComb (fun j => PowerSeries.C (R := A) (U j)) v (v₀ τ k) := fun τ k => by
      have ht : GtTanR (e τ k) :=
        ((_root_.GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y A b a χ W (e τ k)).2 _ (hv₀ τ k)).2 ((hB τ).1 k).1
      obtain ⟨U, hU, -⟩ := hcomb _ ht
      exact ⟨U, (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W g U e₁ (e τ k) v _ (fun i => (hev i).2) hU).1 (hv₀ τ k)⟩
    choose U hU using hU
    choose u hu using fun τ k => exists_lift ι m2.cart (v₀ τ k)
    choose v' hv' using fun j => exists_lift ι m2.cart (v j)
    have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange ι m2.cart hv hv'
    have hU' : ∀ τ k, IsLieComb (fun j => (ι.comp (PowerSeries.C (R := A))) (U τ k j)) v' (u τ k) := fun τ k =>
      Chart.comb_baseChange ι m2.cart (hU τ k) hv' (hu τ k)
    have hM' : ∀ x i, IsLieComb ((M x).map (ι.comp (PowerSeries.C (R := A))) i) v' (v' i ≫ t'.act.act x) := fun x i =>
      Chart.comb_baseChange ι m2.cart (hM x i) hv' (by
        rw [Over.comp_left, Category.assoc, m2.act, ← Category.assoc, hv', Category.assoc, Over.comp_left])
    have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v (v i ≫ W.t.act.act x) := hM
    have hUe : ∀ τ k x, U τ k ᵥ* M x = ρ τ x • U τ k := fun τ k x => by
      have := (eig_iff hy hv _ (hMR x) (hU τ k) _).1 (((hB τ).1 k).2 x)
      funext j
      have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun this j)
      simpa [Matrix.vecMul, dotProduct] using this
    refine ⟨u, fun τ k => ⟨v₀ τ k, hv₀ τ k, hu τ k⟩, fun τ => ⟨fun k => ⟨isTangent_of_comb hy' hb'.1 (hU' τ k), fun x => ?_⟩,
      fun w hw hwe => ?_⟩⟩
    · refine (eig_iff hy' hb' _ (hM' x) (hU' τ k) _).2 ?_
      funext j
      have := congrArg (ι.comp (PowerSeries.C (R := A))) (congrFun (hUe τ k x) j)
      simpa [Matrix.vecMul, dotProduct] using this
    · obtain ⟨z, hz, -⟩ := hb'.2 w hw
      simp only [comb_iff hy' hb' (hU' τ) hz]
      refine eig_powerSeries M (fun x => ρ τ x) (U τ) (hUe τ) (fun s hs => ?_) _ hflat z
        (fun x => (eig_iff hy' hb' _ (hM' x) hz _).1 (hwe x))
      have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
      have := (hB τ).2 _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
      simpa only [comb_iff hy hv (hU τ) hc] using this
  obtain ⟨u, hu, hb⟩ := arcBasis_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e h (PowerSeries A')
    (PowerSeries.map f) hfl W'.t m
  refine ⟨W', e', he', u, fun τ k => ?_, fun τ => ?_⟩
  · obtain ⟨v, hv, huv⟩ := hu τ k
    exact hm _ _ v _ (he' τ k) hv huv
  · simpa only [PowerSeries.map_C, RingHom.comp_apply] using hb τ

theorem mem_of_isIntegral {F : Type} [Field F] (V : ValuationSubring F) {x : F} (h : IsIntegral ℤ x) : x ∈ V := by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 h.tower_top
  exact hy ▸ y.2

theorem exists_values (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  have key : ∀ (x : c.F) (n : ℕ), 0 < n → ∀ m : ℤ, x ^ n = m → x ∈ c.V W := fun x n hn m h =>
    mem_of_isIntegral _ (IsIntegral.of_pow hn (by
      rw [h]; simpa using isIntegral_algebraMap (R := ℤ) (A := c.F) (x := m)))
  refine ⟨⟨⟨_, GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c⟩, key _ 2 two_pos (-(H.d : ℤ)) ?_⟩,
    ⟨⟨_, GlobalTheory.HostModel.zeta_A_mem_coeff c⟩, key _ l.A l.A_pos 1 ?_⟩, rfl, rfl⟩
  · apply Subtype.ext
    simpa using H.sqrt_neg_disc_sq
  · apply Subtype.ext
    simpa [zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one

def embV (c : Coeff l) (W : ValuationSubring ℂ) (τ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c τ).codRestrict (c.V W).toSubring fun x =>
    mem_of_isIntegral _ ((RingOfIntegers.isIntegral x).map (embK c τ).toIntAlgHom)

end GlobalTheory.IntModelExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaximalCuspsNoLowCoefficientIffFourierJacobi
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

namespace GlobalTheory.MaxCuspRecord

theorem mem_MggK_of_rho_eq_zero {D : D7} (X : WeightFamilies.Prov D) (CR Tt cc : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (h0 : WeightFamilies.rho D j = 0) (F : X.Cusp j ka) : F ∈ WeightFamilies.MggK X CR Tt cc j ka := by
  unfold WeightFamilies.MggK
  simp only [Submodule.mem_iInf]
  rintro cu χ ⟨xi, -, hne, -⟩
  exact absurd (funext fun i => absurd i.isLt (by omega)) hne


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tieMaxCusp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), TieMaxCuspSt h j CR Tt cc ka := by
  intro D T h j hj ka CR Tt cc F
  rcases lt_or_eq_of_le hj.2 with hlt | hjm
  · exact (_root_.GlobalTheory.LowCoeff.mem_iff_low_coeff_vanish D T.toCore h.toLawsCore j ka CR Tt cc hj hlt F).2
  · have h0 : WeightFamilies.rho D j = 0 := by
      show D.R.m - j = 0
      omega
    refine ⟨fun _ k => ?_, fun _ => mem_MggK_of_rho_eq_zero _ CR Tt cc j ka h0 F⟩
    have hU : IsUnf (T.U j T.σ₀) := h.unf j hj T.σ₀ T.good_σ₀
    have hq : (T.Q.Dw j).q = 0 := (h.pins.2.2.2 j hj).2.1.trans h0
    have hp0 : ((T.U j T.σ₀).X k).p0 = 0 := ((hU.2.1 k).1).trans hq
    have hFc : (F.1 : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n := cutR_le T.C j ka F.2
    have hcusp := ((mem_cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n F.1).1 hFc).2 T.σ₀ T.good_σ₀
    exact ⟨Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds _ _ hcusp k, fun ξ hξ =>
      absurd hξ (GlobalTheory.PoincareSeriesCompare.not_isIso_of_definite _ (Or.inl hp0) ξ)⟩

end GlobalTheory.MaxCuspRecord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemRangeOfLetBC
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.IntLetterCoord

open Matrix GlobalTheory.BasisUniv

theorem mem_range_of_comb {A K : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] {I : Type} {g m : ℕ} (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A) (U : Fin m → Fin g → A)
    (hU : ∀ k i, U k ᵥ* M i = ρ i • U k)
    (h : ∀ w : Fin g → PowerSeries A, (∀ i, w ᵥ* (M i).map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) (ρ i) • w) →
      ∃! cf : Fin m → PowerSeries A, w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j))
    (z : Fin g → A) (y : Fin m → K) (hz : (fun j => algebraMap A K (z j)) = ∑ k, y k • fun j => algebraMap A K (U k j))
    (k : Fin m) : y k ∈ Set.range (algebraMap A K) := by
  have hK : ∀ i, (fun j => algebraMap A K (z j)) ᵥ* (M i).map (algebraMap A K) =
      algebraMap A K (ρ i) • fun j => algebraMap A K (z j) := fun i => by
    have e : ∀ k, (fun j => algebraMap A K (U k j)) ᵥ* (M i).map (algebraMap A K) =
        algebraMap A K (ρ i) • fun j => algebraMap A K (U k j) := fun k => by
      funext j
      have := congrArg (algebraMap A K) (congrFun (hU k i) j)
      simpa [Matrix.vecMul, dotProduct] using this
    rw [hz, Matrix.sum_vecMul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_vecMul, e, smul_comm]
  have hA : ∀ i, z ᵥ* (M i).map (RingHom.id A) = RingHom.id A (ρ i) • z := fun i => by
    funext j
    apply IsFractionRing.injective A K
    have := congrFun (hK i) j
    simpa [Matrix.vecMul, dotProduct] using this
  have hfl : (algebraMap A K).Flat :=
    RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors A))
  obtain ⟨cf, hcf, -⟩ := eig_powerSeries M ρ U hU h (RingHom.id A) (RingHom.Flat.id A) z hA
  have := (eig_powerSeries M ρ U hU h (algebraMap A K) hfl _ hK).unique (y₂ := fun k => algebraMap A K (cf k)) hz (by
    funext j
    have := congrArg (algebraMap A K) (congrFun hcf j)
    simpa [Finset.sum_apply, Algebra.smul_def] using this)
  exact ⟨cf k, (congrFun this k).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem mem_range_of_letBC (hL : Out.Laws) (hL₂ : Out.Laws2) (hU : Out.UnifBaseChangeSt) (hL₅ : Out.Laws5)
    {A K : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {b : O →+* A} {b' : O →+* K}
    {a : ArcIn Dw l β A b} {a' : ArcIn Dw l β K b'}
    {p : Out.IsPullDeg (algebraMap A K) a.D₀ a'.D₀} (hp : InBC (algebraMap A K) a a' p)
    {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (hB : ArcBasis W ρ e) (τ : E →+* ℂ) {e₁ : Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR K)}
    (he : ∀ k, LetBC p (e τ k) (e₁ k)) {ν : Out.GtPt a.D₀ (epsR A)} {ν₁ e₂ : Out.GtPt a'.D₀ (epsR K)}
    (hν : GtTanR ν) (hν₁ : LetBC p ν ν₁) {y : Fin (Dw.mult τ) → K} (h₂ : GtComb y e₁ e₂) {x : K}
    (hx : GtComb ![x] ![e₂] ν₁) (k : Fin (Dw.mult τ)) : x * y k ∈ Set.range (algebraMap A K) := by
  have hG := hL.globalFns
  have hf : Function.Injective (algebraMap A K) := IsFractionRing.injective _ _
  obtain ⟨hW, -⟩ := (GlobalTheory.ArcQBC.baseChanges hL hL₂ hU hL₅ E H Dw l Xo c O β Y A K b a _ hf b' hp.1).2 a' p hp
  obtain ⟨W', hW'⟩ := hW χ W
  obtain ⟨m, -, hm, -⟩ := GlobalTheory.ArcBaseChange.main hL hL₂ E H Dw l Xo c O β Y A b a χ W K b' a' _ p W' hp hW'
  obtain ⟨v₀, hv₀, hB⟩ := hB
  obtain ⟨g, s, v, M, hev, hv, hcomb, hM⟩ := GlobalTheory.ConstLie.exists_const_basis hG E H Dw l Xo c O β Y A b a χ W
  have ex := GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y A b a χ W
  have ex' := GlobalTheory.ConstLie.main hG E H Dw l Xo c O β Y K b' a' _ W'
  have lin := GlobalTheory.ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y A b a χ W
  have lin' := GlobalTheory.ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y K b' a' _ W'
  have hsm : Smooth W.t.G.hom := W.t.semi.smooth
  have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
  obtain ⟨n, j, hy⟩ := Chart.univChartLoc W.t.G
  obtain ⟨n', j', hy'⟩ := exists_chart_of_pullback _ m.cart
  choose v' hv' using fun j => exists_lift _ m.cart (v j)
  have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange _ m.cart hv hv'
  have coord : ∀ ξ ξ' w, GtTanR ξ → LieImg W ξ w → LetBC p ξ ξ' → ∃ (z : Fin g → A) (w' : epsR (PowerSeries K) ⟶ W'.t.G),
      IsLieComb (fun j => PowerSeries.C (R := A) (z j)) v w ∧ LieImg W' ξ' w' ∧
      IsLieComb (fun j => PowerSeries.C (R := K) (algebraMap A K (z j))) v' w' := fun ξ ξ' w ht hw hξ => by
    obtain ⟨z, hz, -⟩ := hcomb _ ht
    have h1 := (lin g z s ξ v w (fun i => (hev i).2) hz).1 hw
    obtain ⟨w', hw'⟩ := exists_lift _ m.cart w
    refine ⟨z, w', h1, hm _ _ w w' hξ hw hw', ?_⟩
    simpa only [PowerSeries.map_C] using Chart.comb_baseChange _ m.cart h1 hv' hw'
  choose U u hU₀ hu hU' using fun k => coord _ _ _ (((ex (e τ k)).2 _ (hv₀ τ k)).2 ((hB τ).1 k).1) (hv₀ τ k) (he k)
  obtain ⟨w, hw⟩ := (ex ν).1.exists
  obtain ⟨z, w', -, hw', hz'⟩ := coord _ _ _ hν hw hν₁
  obtain ⟨w₂, hw₂⟩ := (ex' e₂).1.exists
  have c₂ := (lin' _ y e₁ e₂ u w₂ hu h₂).1 hw₂
  have c₁ := (lin' _ ![x] ![e₂] ν₁ (fun _ => w₂) w' (fun i => by fin_cases i; exact hw₂) hx).1 hw'
  have d₂ : IsLieComb (∑ k, PowerSeries.C (R := K) (y k) • fun j => PowerSeries.C (R := K) (algebraMap A K (U k j)))
      v' w₂ := by
    have hc := (Chart.isLieComb_iff (∑ k, PowerSeries.C (R := K) (y k) •
      fun j => PowerSeries.C (R := K) (algebraMap A K (U k j))) v' _).2 rfl
    have := (comb_iff hy' hb' hU' hc _).2 rfl
    rwa [((Chart.isLieComb_iff _ _ _).1 this).trans ((Chart.isLieComb_iff _ _ _).1 c₂).symm] at hc
  have d₁ := (comb_iff hy' hb' (u := fun _ : Fin 1 => w₂) (fun _ => d₂) hz' _).1 c₁
  have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v (v i ≫ W.t.act.act x) := hM
  have hUe : ∀ k x, U k ᵥ* M x = ρ τ x • U k := fun k x => by
    have := (eig_iff hy hv _ (hMR x) (hU₀ k) _).1 (((hB τ).1 k).2 x)
    funext j
    have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun this j)
    simpa [Matrix.vecMul, dotProduct] using this
  refine mem_range_of_comb M (fun x => ρ τ x) U hUe (fun s hs => ?_) z (fun k => x * y k) ?_ k
  · have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
    have := (hB τ).2 _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
    simpa only [comb_iff hy hv hU₀ hc] using this
  · funext i
    have := congrArg (PowerSeries.constantCoeff (R := K)) (congrFun d₁ i)
    simpa [Finset.sum_apply, Finset.mul_sum, _root_.mul_assoc] using this

theorem main : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (Yw : Model Xo c (c.V Wl).subtype), Yw.N4 → (∀ (χ : Sp (PowerSeries Tv.V) ⟶ Yw.X) (W : Wit Yw M.aw χ), ArcBasis W M.ρ M.ew) → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) (x : Tv.Fr), (∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![x] ![e₂] ν₁) → ∀ m, x * M.g τ k m ∈ Set.range (algebraMap Tv.V Tv.Fr) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d Tv io Wl M Yw hN hB τ k x ⟨ν, ν₁, e₂, hν, hν₁, he₂, hx⟩ m
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  obtain ⟨χ₀, hχ₀, -⟩ := hN Tv.V M.b ϖ M.aw (Or.inr ⟨inferInstance, hϖ, by
    rw [← hϖ.maximalIdeal_eq]; infer_instance⟩)
  obtain ⟨W₀⟩ := (Yw.hasArcData_iff _ _ _ _ _).1 ((hχ₀ χ₀).1 rfl).2.2.2
  obtain ⟨e₁, e₂', l₁, l₂, -, hg⟩ := M.e_tie
  have hK' : InBC io (d.a.restrict (c.V d.Wp).subtype) (M.aK.restrict (c.V d.Wp).subtype) M.pK := ⟨rfl, M.bcK.2⟩
  obtain ⟨-, x₂, -⟩ :=
    (GlobalTheory.ArcQBC.baseChanges hK.laws hK.laws2 hK.ubc hK.laws5 E H Dw l Xo c _ _ d.Y K₁ Tv.Fr _
      (d.a.restrict (c.V d.Wp).subtype) io io.injective _ hK'.1).2 (M.aK.restrict (c.V d.Wp).subtype) M.pK hK'
  obtain rfl : e₂ = e₂' τ k := (x₂ (d.e τ k)).unique he₂ (l₂ τ k)
  exact mem_range_of_letBC hK.laws hK.laws2 hK.ubc hK.laws5 M.bcw W₀ (hB χ₀ W₀) τ (l₁ τ) hν hν₁ (hg τ k) hx m

end GlobalTheory.IntLetterCoord
end
end

