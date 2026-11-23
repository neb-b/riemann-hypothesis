module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem finite_notMem_coheight_le_one {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : {ξ : X | ξ ∉ U ∧ Order.coheight ξ ≤ 1}.Finite := by
  obtain ⟨S, hS, hcl, hirr, hun⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  have hg : genericPoint X ∈ U := (genericPoint_specializes hU.some).mem_open U.isOpen hU.some_mem
  refine (hS.biUnion (t := fun C => {κ | IsGenericPoint κ C}) fun C _ =>
    Set.Subsingleton.finite fun _ h _ h' => h.eq h').subset ?_
  rintro ξ ⟨hξ, h1⟩
  obtain ⟨C, hC, hξC⟩ : ξ ∈ ⋃₀ S := hun ▸ hξ
  obtain ⟨κ, hκ⟩ := QuasiSober.sober (hirr C hC) (hcl C hC)
  have hκU : κ ∈ (U : Set X)ᶜ := hun ▸ ⟨C, hC, hκ.mem⟩
  refine Set.mem_biUnion hC ?_
  by_cases h : ξ ⤳ κ
  · rwa [(h.antisymm (hκ.specializes hξC)).eq]
  · have hlt : ξ < κ := lt_of_le_not_ge (hκ.specializes hξC) h
    have hlt' : κ < genericPoint X := lt_of_le_not_ge (genericPoint_specializes κ)
      fun h' => hκU (((genericPoint_specializes κ).antisymm h').eq ▸ hg)
    have h2 := (add_le_add_left (le_add_self.trans (Order.coheight_add_one_le hlt')) 1).trans
      ((Order.coheight_add_one_le hlt).trans h1)
    exact absurd h2 (by decide)

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isNoetherian [IsNoetherianRing o] : IsNoetherian M.Z :=
  have := M.lft
  have := M.qc
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  {}

theorem isNoetherianRing_O [IsNoetherianRing o] (z : M.Z) : IsNoetherianRing (M.O z) :=
  have := M.isNoetherian
  isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

theorem coheight_le_one_of_valuationRing [IsNoetherianRing o] {ξ : M.Z} (h : ValuationRing (M.O ξ)) :
    Order.coheight ξ ≤ 1 := by
  have := M.isNoetherianRing_O ξ
  have : IsPrincipalIdealRing (M.O ξ) := IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
  have h1 : ringKrullDim (M.O ξ) ≤ 1 := Ring.krullDimLE_iff.1 inferInstance
  rw [← ringKrullDim_eq_of_ringEquiv (M.stalkEquiv ξ), ringKrullDim_stalk_eq_coheight] at h1
  exact_mod_cast h1

theorem exists_specializes_isLocalization (z : M.Z) (q : Ideal (M.O z)) [q.IsPrime] :
    ∃ (ξ : M.Z) (h : ξ ⤳ z),
      letI := (Subalgebra.inclusion (O_le_of_specializes h)).toRingHom.toAlgebra
      IsLocalization.AtPrime (M.O ξ) q := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  let ψ : ∀ {x : M.Z} (_ : x ∈ V), Γ(M.Z, V) →+* M.O x := fun {x} hx =>
    (M.stalkEquiv x).toRingHom.comp (M.Z.presheaf.germ V x hx).hom
  have hψ : ∀ {x : M.Z} (hx : x ∈ V) (f : Γ(M.Z, V)), ψ hx f = ⟨valF M.pt V f, valF_mem_O hx f⟩ :=
    fun hx f => stalkEquiv_germ hx f
  have hloc : ∀ (p : PrimeSpectrum Γ(M.Z, V)) (hp : hV.fromSpec p ∈ V),
      @IsLocalization.AtPrime _ _ (M.O (hV.fromSpec p)) _ (ψ hp).toAlgebra p.asIdeal _ := fun p hp => by
    let : Algebra Γ(M.Z, V) (M.Z.presheaf.stalk (hV.fromSpec p)) :=
      TopCat.Presheaf.algebra_section_stalk M.Z.presheaf (U := V) ⟨_, hp⟩
    let := (ψ hp).toAlgebra
    have : IsLocalization p.asIdeal.primeCompl (M.Z.presheaf.stalk (hV.fromSpec p)) :=
      hV.isLocalization_stalk' p hp
    exact IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl
      ({ M.stalkEquiv _ with commutes' := fun _ => rfl } :
        M.Z.presheaf.stalk (hV.fromSpec p) ≃ₐ[Γ(M.Z, V)] M.O (hV.fromSpec p))
  have hmem : ∀ p : PrimeSpectrum Γ(M.Z, V), hV.fromSpec p ∈ V := fun p => by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨p₀, rfl⟩ : ∃ p₀ : PrimeSpectrum Γ(M.Z, V), hV.fromSpec p₀ = z :=
    (hV.range_fromSpec ▸ hz : z ∈ Set.range hV.fromSpec)
  let := (ψ hz).toAlgebra
  have h₀ := hloc p₀ hz
  let p : PrimeSpectrum Γ(M.Z, V) := ⟨q.comap (ψ hz), inferInstance⟩
  have hle : p.asIdeal ≤ p₀.asIdeal := fun a ha =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (M.O (hV.fromSpec p₀)) p₀.asIdeal a).1
      (IsLocalRing.le_maximalIdeal_of_isPrime q ha)
  have hs : hV.fromSpec p ⤳ hV.fromSpec p₀ :=
    ((PrimeSpectrum.le_iff_specializes p p₀).1 hle).map hV.fromSpec.continuous
  refine ⟨_, hs, ?_⟩
  let := (Subalgebra.inclusion (O_le_of_specializes hs)).toRingHom.toAlgebra
  let := (ψ (hmem p)).toAlgebra
  have h₁ := hloc p (hmem p)
  have : IsScalarTower Γ(M.Z, V) (M.O (hV.fromSpec p₀)) (M.O (hV.fromSpec p)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hψ (hmem p) a).trans
      (congrArg (Subalgebra.inclusion (O_le_of_specializes hs)) (hψ hz a)).symm
  have h₂ := IsLocalization.isLocalization_of_submonoid_le (M.O (hV.fromSpec p₀)) (M.O (hV.fromSpec p))
    p₀.asIdeal.primeCompl p.asIdeal.primeCompl (fun a ha h => ha (hle h))
  refine IsLocalization.of_le_of_exists_dvd (p.asIdeal.primeCompl.map (algebraMap _ (M.O (hV.fromSpec p₀)))) _
    (by rintro _ ⟨a, ha, rfl⟩; exact ha) fun n hn => ?_
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj p₀.asIdeal.primeCompl n
  refine ⟨_, ⟨a, fun ha => ?_, rfl⟩, _, e.symm⟩
  have ha' : algebraMap _ (M.O (hV.fromSpec p₀)) a ∈ q := ha
  rw [← e] at ha'
  exact hn ((Ideal.mul_unit_mem_iff_mem q (IsLocalization.map_units _ s)).1 ha')

theorem mem_O_of_forall_valuationRing [IsNoetherianRing o] (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    (z : M.Z) (φ : Ω) (h : ∀ ξ : M.Z, ξ ⤳ z → ValuationRing (M.O ξ) → φ ∈ M.O ξ) : φ ∈ M.O z := by
  have := M.isNoetherianRing_O z
  have := isIntegrallyClosed_O hn z
  obtain ⟨y, rfl⟩ : φ ∈ (algebraMap (M.O z) Ω).range := by
    refine (mem_range_algebraMap_iff_forall_height_eq_one φ).mpr fun q _ h1 => ?_
    obtain ⟨ξ, hξ, hloc⟩ := M.exists_specializes_isLocalization z q
    let := (Subalgebra.inclusion (O_le_of_specializes hξ)).toRingHom.toAlgebra
    have : IsScalarTower (M.O z) (M.O ξ) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have := isDiscreteValuationRing_of_height_eq_one q h1 (M.O ξ)
    exact (mem_range_algebraMap_iff_mem_primeLocalSubalgebra q (M.O ξ) φ).mp
      ⟨⟨φ, h ξ hξ inferInstance⟩, rfl⟩
  exact y.2

end RatModel

theorem normalModel_height_le_one :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (z : M.Z),
      (∀ φ : Ω, (∀ ξ : M.Z, ξ ⤳ z → ValuationRing (M.O ξ) → φ ∈ M.O ξ) → φ ∈ M.O z) ∧
      IsNoetherianRing (M.O z) ∧
      ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → {ξ : M.Z | ξ ∉ U ∧ ValuationRing (M.O ξ)}.Finite := by
  intro o Ω _ _ _ M _ hn z
  have := M.isNoetherian
  exact ⟨M.mem_O_of_forall_valuationRing hn z, M.isNoetherianRing_O z, fun U hU =>
    (finite_notMem_coheight_le_one U hU).subset fun _ h => ⟨h.1, M.coheight_le_one_of_valuationRing h.2⟩⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWitOfPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WitnessMove

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}


set_option maxHeartbeats 1600000 in
theorem unif_move (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (t : SAB H (Sp R)) (m : SABMap t Y.t χ)
    (W' : ArcWit Y a I f u χ) (ψ : t.G ≅ W'.t.G)
    [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ W'.m.φ = m.φ) (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) :
    ∃ (bc : t.G ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W'.t.G) (D'' : Out.DegData R I)
      (hD : Out.IsPullDeg (RingHom.id R) W'.P.D.toPre D''.toPre) (U'' : Out.Unif I D'' W'.P.A t.G)
      (_ : Module (𝓞 E) D''.toPre.X) (oD : letI := H.starRing; D''.toPre.OAct (𝓞 E)),
      IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = ψ.hom.left ∧
      U''.LG = t.PP ∧
      U''.gen.hom.left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
        pullback.fst t.G.hom (Out.jK R) ≫ ψ.hom.left ∧
      Out.IsPullUnif (RingHom.id R) hD bc W'.P.U U'' ∧
      (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧
      (letI := H.starRing; ∀ x, oD.onB.act x ≫ hD.e.hom =
        hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.P.oD.onB.act x)) ∧
      (letI := H.starRing; U''.toUnifPre.OLinear (𝓞 E) oD W'.P.oA t.act.toRingAct) ∧
      (letI := H.starRing; TraceFormTwistIso D''.toPre oD H.w0) := by
  let _ := H.starRing
  have hs := specOf_id R
  have gp₁ : IsGrpPullback t.G W'.t.G (Out.specOf (RingHom.id R)) ψ.hom.left :=
    (isGrpPullback_of_iso ψ).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback W'.t.G (Out.specOf (RingHom.id R)))
  have gpG : IsGrpPullback W'.P.A.A W'.t.G (Out.jK R) (W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R)) := by
    have := W'.P.U.gen_hom
    have : IsMonHom W'.P.U.gen.symm.hom := by show IsMonHom W'.P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso W'.P.U.gen.symm).comp (isGrpPullback_pullback W'.t.G (Out.jK R))).congr
      (Category.id_comp _) rfl
  have gp₂ : IsGrpPullback ((Over.pullback (Out.jK R)).obj t.G) W'.t.G (Out.jK R)
      (pullback.fst t.G.hom (Out.jK R) ≫ ψ.hom.left) :=
    ((isGrpPullback_pullback t.G (Out.jK R)).comp (isGrpPullback_of_iso ψ)).congr (Category.comp_id _) rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp₂ gpG
  have hgi : W'.P.U.gen.inv.left ≫ W'.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (W'.P.A.L.pull eA.hom.left) (W'.P.U.LG.L.pull (pullback.fst t.G.hom (Out.jK R) ≫ bc.hom.left ≫
      pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := eA.hom.left ≫ W'.P.U.gen.inv.left)
      (chartPullSame W'.P.A.L (fun _ => eA.hom.left) (fun _ => W'.P.U.gen.hom.left) _ _ fun _ => by
        rw [Category.assoc, hgi, Category.comp_id])
      (chartPullSame W'.P.U.LG.L _ (fun _ => pullback.fst W'.t.G.hom (Out.jK R)) _ _ fun _ => by
        rw [hbc, ← heA]; simp only [Category.assoc]) W'.P.U.ext
  obtain ⟨wL', he', gL, rL⟩ := rigIso_congr W'.P.bundle (CubeMap.ofHom ψ.hom) (sabMap_cubical m W'.m ψ hφ) hbc
    (e := Out.specOf (RingHom.id R)) hs
  obtain ⟨Wo, hWo, hψW⟩ := h5.psiOnExists R I hR W'.P.D
  have hgen : (Out.specOf (RingHom.id R)).base (genericPoint (Spec (CommRingCat.of R))) ∈ Wo := by
    rw [hs]; exact hWo
  have hI : I.map (RingHom.id R) ≤ I := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', hLG, hgenU, hPU⟩ := hU R R I I hR hR (RingHom.id R) hI W'.P.D W'.P.A W'.t.G W'.t.semi W'.P.U
    Wo hψW hgen t.G bc mbc W'.P.A rfl eA mE wA t.PP wL' he' gL rL
  have hbcact : ∀ x, t.act.toRingAct.act x ≫ bc.hom =
      bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.toRingAct.act x) := by
    intro x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫
          pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = pullback.fst _ _ ≫ (W'.t.act.act x).left :=
        pullback.lift_fst _ _ _
      show (t.act.act x ≫ bc.hom).left ≫ _ =
        (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, hbc, ← Category.assoc, hbc,
        ← Over.comp_left, hact, Over.comp_left]
    · exact (Over.w (t.act.act x ≫ bc.hom)).trans
        (Over.w (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x))).symm
  have actA : ∀ x, (W'.P.oA.act x).left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
      W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) ≫ (W'.t.act.act x).left := by
    intro x
    have e : W'.P.oA.act x ≫ W'.P.U.gen.inv = W'.P.U.gen.inv ≫ (Over.pullback (Out.jK R)).map (W'.t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (W'.P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (Out.jK R)).map (t.act.toRingAct.act x) ≫ U''.gen.hom =
      U''.gen.hom ≫ W'.P.oA.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply gpG.1.hom_ext
    · have a₁ : ((Over.pullback (Out.jK R)).map (t.act.act x)).left ≫ pullback.fst t.G.hom (Out.jK R) =
          pullback.fst t.G.hom (Out.jK R) ≫ (t.act.act x).left := pullback.lift_fst _ _ _
      have a₃ : (t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (W'.t.act.act x).left := by
        rw [← Over.comp_left, hact, Over.comp_left]
      show ((Over.pullback (Out.jK R)).map (t.act.act x) ≫ eA.hom).left ≫ _ = (eA.hom ≫ W'.P.oA.act x).left ≫ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₃, Over.comp_left,
        Category.assoc, actA, reassoc_of% heA]
    · rw [Over.w, Over.w]
  obtain ⟨mod'', oD'', xl, el, lin'', w0''⟩ := h5.oLinBaseChange R R I I hR hR (RingHom.id R) W'.P.D W'.P.A W'.t.G W'.P.U
    t.G bc mbc W'.P.A D'' hD U'' hPU (𝓞 E) W'.P.oD W'.P.oA W'.t.act.toRingAct W'.P.lin t.act.toRingAct hbcact
    W'.P.oA extA
  refine ⟨bc, D'', hD, U'', mod'', oD'', mbc, hbc, hLG, ?_, hPU, xl, el, lin'', w0'' H.w0 W'.P.w0⟩
  rw [hgenU]; exact heA


set_option maxHeartbeats 1600000 in
theorem exists_wit_of_pull (h5 : Out.Laws5) (hQ : QkPullExistsSt) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) (t : SAB H (Sp R))
    (m : SABMap t Y.t χ) (P : PELUnif I t)
    (bc : t.G ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W.t.G) [IsMonHom bc.hom]
    (hbc : bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf (RingHom.id R)) ≫ W.m.φ = m.φ)
    (hD : Out.IsPullDeg (RingHom.id R) W.P.D.toPre P.D.toPre) (hPU : Out.IsPullUnif (RingHom.id R) hD bc W.P.U P.U)
    (xl : ∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y)
    (el : letI := H.starRing; ∀ x, P.oD.onB.act x ≫ hD.e.hom =
      hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W.P.oD.onB.act x)) :
    ∃ W' : ArcWit Y a I f u χ, W'.t = t ∧ HEq W'.m m ∧ HEq W'.P P := by
  letI := H.starRing
  obtain ⟨he, w, e, -, -, d1, d2, d3, d4, d5, d6⟩ := ArcWit.witMove h5 hQ hR W P.U P.oD bc hD hPU xl el
  refine ⟨⟨t, m, P, _, he, w, e, d1, d2, d3, d4, d5, fun F _ _ _ _ uF h1 h2 => ⟨(d6 F uF h1 h2).1,
    fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => (d6 F uF h1 h2).2 yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 ?_⟩⟩,
    rfl, HEq.rfl, HEq.rfl⟩
  rw [hbc]; exact e4


set_option maxHeartbeats 1600000 in
theorem exists_wit (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5) (h6 : Out.UnifUniqSt) (hQ : QkPullExistsSt)
    {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type}
    [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} (hR : Out.AdmBase R I) {f : O' →+* R} {u : R}
    {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t) :
    ∃ W' : ArcWit Y a I f u χ, W'.t = t ∧ HEq W'.m m ∧ HEq W'.P P := by
  letI := H.starRing
  have hs := specOf_id R
  obtain ⟨ψ, hψ, hφ, hact, -⟩ := sabMap_iso m W.m rfl rfl
  obtain ⟨bc, D'', hD₂, U'', mod'', oD'', mbc, hbc, hLG, -, hPU₂, xl₂, el₂, lin'', w0''⟩ :=
    unif_move hU h5 hR t m W ψ hφ hact
  let P'' : PELUnif I t :=
    { D := D'', mod := mod'', oD := oD'', A := W.P.A, oA := W.P.oA, U := U'', bundle := hLG, lin := lin'', w0 := w0'' }
  obtain ⟨⟨t₁, m₁, P₁, φ₁, he₁, w₁, e₁, s₁⟩, rfl, hm₁, hP₁⟩ := exists_wit_of_pull h5 hQ hR W t m P'' bc
    (by rw [reassoc_of% hbc, hφ]) hD₂ hPU₂ xl₂ el₂
  obtain rfl : m₁ = m := eq_of_heq hm₁
  clear hP₁
  have res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U)
      (x : Γ(X, U)ˣ) : res h (res h' x) = res (h.trans h') x := by
    have e : X.presheaf.map (homOfLE h').op ≫ X.presheaf.map (homOfLE h).op =
        X.presheaf.map (homOfLE (h.trans h')).op := by
      rw [← Functor.map_comp]
      rfl
    apply Units.ext
    exact congrArg (fun φ => φ.hom (x : Γ(X, U))) e

  have res_g_mul_res_g_eq_res_g_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
      (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
      res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
    have hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
    have key := congrArg (⇑(res hW)) (hL.cocycle i j k)
    simp only [map_mul, res_res_lemma] at key
    exact key

  have isGen_g_iso_self_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
      (⟨fun p : L.ι × L.ι => L.g p.1 p.2⟩ : LB.Iso L L).IsGen := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
    have h₀ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U p₂ := inf_le_left
    have h₁ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₁ :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    have h₂ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U q₁ ⊓ L.U q₂ := inf_le_right
    have h₃ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₂ :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
    have h₄ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₂ ⊓ L.U q₂ :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    have c₁ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ q₁ q₂ h₁ h₂ h₃
    have c₂ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ p₂ q₂ h₀ h₄ h₃
    have key : res h₀ (L.g p₁ p₂) =
        res h₁ (L.g p₁ q₁) * (res h₄ (L.g p₂ q₂))⁻¹ * res h₂ (L.g q₁ q₂) := by
      rw [mul_right_comm, c₁, ← c₂, mul_inv_cancel_right]
    exact key

  have exists_iso_pair_of_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G}
      (h : L₁ = L₂) :
      ∃ (w : LB.Iso L₁.L L₂.L) (w' : LB.Iso L₂.L L₁.L), w.IsGen ∧ w'.IsGen ∧
        LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig ∧
        LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₂.rig L₁.rig := by
    cases h
    refine ⟨⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩, ⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩,
      isGen_g_iso_self_of_isLB L₁.isLB, isGen_g_iso_self_of_isLB L₁.isLB, ?_, ?_⟩
    · intro p
      exact L₁.rigGen p.1 p.2
    · intro p
      exact L₁.rigGen p.1 p.2
  obtain ⟨wL₀, -, g₀, -, m₀, -⟩ := exists_iso_pair_of_eq (P.bundle.trans P₁.bundle.symm)
  obtain ⟨hD₁, hlev, holin⟩ := h6 R I hR P₁.D P.D P₁.A P.A t₁.G t₁.semi P₁.U P.U wL₀ g₀ m₀
  obtain ⟨xl₁, el₁⟩ := holin (𝓞 E) P₁.oD P.oD P₁.oA P.oA t₁.act.toRingAct P₁.lin P.lin
  have mR : IsMonHom (Iso.refl t₁.G).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨bc₀, mbc₀, hbc₀⟩ := grpPullback_iso ((isGrpPullback_of_iso (Iso.refl t₁.G)).congr hs.symm rfl)
    (isGrpPullback_pullback t₁.G (Out.specOf (RingHom.id R)))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst t₁.G.hom (Out.specOf (RingHom.id R)) = 𝟙 _ := hbc₀
  have hPU₁ := isPullUnif_of_uniq P₁.U P.U hD₁ wL₀ g₀ m₀ hlev bc₀ hbc₀'
  exact exists_wit_of_pull h5 hQ hR ⟨t₁, m₁, P₁, φ₁, he₁, w₁, e₁, s₁⟩ t₁ m₁ P bc₀
    (by rw [← Category.assoc]; exact (congrArg (· ≫ m₁.φ) hbc₀').trans (Category.id_comp _)) hD₁ hPU₁ xl₁ el₁

end GlobalTheory.WitnessMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem exists_sectionHom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (a : T.left ⟶ S) (ha : a = T.hom ≫ f) :
    ∃ ρ : (T ⟶ G') →* (Over.mk a ⟶ G), (∀ x, (ρ x).left = x.left ≫ φ) ∧ Function.Surjective ρ := by
  subst ha
  refine ⟨pushHom h T, fun _ => rfl, fun c => ?_⟩
  exact ⟨Over.homMk (h.1.lift c.left T.hom (Over.w c)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem eSec_comp_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    eSec G' ≫ φ = (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left) ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem exists_fac_residue (V K : Type) [CommRing V] [IsLocalRing V] [Field K] (r : Sp K ⟶ Sp V)
    (hr : Set.range r = {IsLocalRing.closedPoint V}) :
    ∃ s : Sp K ⟶ Sp (IsLocalRing.ResidueField V), s ≫ spMap (IsLocalRing.residue V) = r := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective r
  have h : PrimeSpectrum.comap ψ.hom (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint V := by
    have : (Spec.map ψ) (IsLocalRing.closedPoint K) ∈ Set.range (Spec.map ψ) := ⟨_, rfl⟩
    rw [hr] at this
    exact this
  let ψ' : V →+* K := ψ.hom
  have : IsLocalHom ψ' := (IsLocalRing.isLocalHom_iff_comap_closedPoint ψ').2 h
  refine ⟨spMap (IsLocalRing.ResidueField.lift ψ'), ?_⟩
  rw [← Spec.map_comp]
  congr 1

theorem Core.Test.exists_isGt_fibre {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (K : Type) [Field K] (r : Sp K ⟶ Sp τ.V) (hr : Set.range r = {IsLocalRing.closedPoint τ.V}) :
    ∃ (G₁ : Over (Sp K)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (E : SplitExt (Sp K)) (φ : G₁.left ⟶ τ.H.left),
      E.IsGt G₁ ∧ IsGrpPullback G₁ τ.H r φ := by
  obtain ⟨s, rfl⟩ := exists_fac_residue τ.V K r hr
  obtain ⟨S, hS⟩ := τ.split
  obtain ⟨E, -, -, -, -, hE⟩ := gtBaseChange _ _ s S _ hS
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue τ.V))).obj τ.H) := Functor.isCommMonObj_obj
  exact ⟨_, _, Functor.isCommMonObj_obj, E, _, hE,
    (isGrpPullback_pullback _ s).comp (isGrpPullback_pullback τ.H _)⟩

theorem Core.Test.eSec_comp_f {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y) :
    (eSec τ.H ≫ τ.f : Sp τ.V ⟶ C.G.toScheme) = τ.y₀ ≫ C.e := by
  have := C.proper
  have : IsSeparated C.GG.hom := inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom))
  have : IsDominant (Out.jK τ.V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective τ.V _)]
    exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated C.GG.hom ?_ (Out.jK τ.V) ?_
  · have h₁ : (eSec τ.H ≫ τ.H.hom : Sp τ.V ⟶ Sp τ.V) = 𝟙 _ := Over.w η[τ.H]
    have h₂ : C.e ≫ C.GG.hom = 𝟙 _ := C.e_sec
    rw [Category.assoc, Category.assoc, τ.f_over, h₂, Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.y₀) h₁).trans (Category.id_comp _))
  · have h₁ := @eSec_comp_of_isGrpPullback _ _ _ _ (_) (_) _ _ τ.φ_cart
    have h₂ := eSec_comp_of_isGrpPullback (isGrpPullback_pullback τ.H (Out.jK τ.V))
    rw [← reassoc_of% τ.yK_fac, C.e_zero]
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ C.a) h₁) |>.trans (Category.assoc _ _ _))
    rw [τ.φ_f]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.f) h₂.symm).trans (Category.assoc _ _ _))

theorem Core.fibLaw_of_testCart : ∀ C : Core, C.TestCart → C.FibLaw := by
  intro C hC p _ y y' τ τ' K _ _ r r' hr hr' hy c d c' d' hc hd
  obtain ⟨G₁, _, _, E₁, φ₁, g₁, h₁⟩ := τ.exists_isGt_fibre K r hr
  obtain ⟨G₂, _, _, E₂, φ₂, g₂, h₂⟩ := τ'.exists_isGt_fibre K r' hr'
  have P₁ := h₁.1.paste_horiz (hC p y τ)
  have P₂ := h₂.1.paste_horiz (hC p y' τ')
  let i : G₁ ⟶ G₂ := Over.homMk (P₂.lift (φ₁ ≫ τ.f) G₁.hom (by rw [P₁.w, hy])) (P₂.lift_snd _ _ _)
  have hi : i.left ≫ φ₂ ≫ τ'.f = φ₁ ≫ τ.f := P₂.lift_fst _ _ _
  have u₁ : η[G₁].left ≫ φ₁ ≫ τ.f = (r ≫ τ.y₀ ≫ C.e : Sp K ⟶ C.G.toScheme) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.f) (eSec_comp_of_isGrpPullback h₁)).trans
      ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) τ.eSec_comp_f)))
  have u₂ : η[G₂].left ≫ φ₂ ≫ τ'.f = (r' ≫ τ'.y₀ ≫ C.e : Sp K ⟶ C.G.toScheme) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ'.f) (eSec_comp_of_isGrpPullback h₂)).trans
      ((Category.assoc _ _ _).trans (congrArg (r' ≫ ·) τ'.eSec_comp_f)))
  have hone : η[G₁] ≫ i = η[G₂] := by
    apply Over.OverMorphism.ext
    apply P₂.hom_ext
    · rw [Over.comp_left, Category.assoc, hi, u₁, u₂]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C.e) hy).trans (Category.assoc _ _ _))
    · rw [Over.w, Over.w]
  have := isMonHom_of_isGt_of_one K E₁ E₂ G₁ G₂ g₁ g₂ i hone
  obtain ⟨ρ₁, l₁, s₁⟩ := exists_sectionHom h₁ (Over.mk (𝟙 _)) r (Category.id_comp _).symm
  obtain ⟨ρ₂, l₂, -⟩ := exists_sectionHom h₂ (Over.mk (𝟙 _)) r' (Category.id_comp _).symm
  have key : ∀ x, (ρ₁ x).left ≫ τ.f = (ρ₂ (x ≫ i)).left ≫ τ'.f := fun x => by
    rw [l₁, l₂, Over.comp_left, Category.assoc, Category.assoc, Category.assoc, hi]
  have inj : ∀ (x) (z : Over.mk r' ⟶ τ'.H), (ρ₁ x).left ≫ τ.f = z.left ≫ τ'.f → z = ρ₂ (x ≫ i) := fun x z hz => by
    apply Over.OverMorphism.ext
    apply (hC p y' τ').hom_ext
    · exact hz.symm.trans (key x)
    · rw [Over.w, Over.w]
  obtain ⟨c, rfl⟩ := s₁ c
  obtain ⟨d, rfl⟩ := s₁ d
  obtain rfl := inj c c' hc
  obtain rfl := inj d d' hd
  constructor
  · rw [← map_mul, ← map_mul, ← MonObj.mul_comp]
    exact key _
  · rw [← map_inv, ← map_inv, ← GrpObj.inv_comp]
    exact key _

end GlobalTheory.ZJ
end

