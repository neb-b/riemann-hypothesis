module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Scalars
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Formalism.LocalToGlobal.Columns.HeckeInertComm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackSectionsProportionalToCombinations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

open TopologicalSpace

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem mem_nonzeroLocus_iff_comb {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} {Ψ : X ⟶ B₀} (hcov : ⨆ i, nonzeroLocus (b i) = ⊤)
    (hG : Generates a φ p c) (hP : Proport a b φ p Ψ c) {z : X} {q : N.ι} (hq : φ z ∈ N.U q) {k : H.ι}
    (hk : Ψ z ∈ H.U k) (i : Fin mB) :
    Ψ z ∈ nonzeroLocus (b i) ↔ IsUnit (comb a φ p c z q i) := by
  obtain ⟨j₀, hj₀⟩ := hG z q hq
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (Ψ z)))
  have u₀ := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i₀) Ψ z hk).1 hi₀
  have e₀ := hP z q k hq hk i₀ j₀
  have ub : IsUnit (gs Ψ z (H.U k) ((b j₀).f k)) := by
    have := u₀.mul hj₀
    rw [e₀] at this
    exact isUnit_of_mul_isUnit_left this
  have e := hP z q k hq hk j₀ i
  rw [GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i) Ψ z hk]
  constructor
  · intro h
    have := h.mul hj₀
    rw [← e] at this
    exact isUnit_of_mul_isUnit_right this
  · intro h
    have := ub.mul h
    rw [e] at this
    exact isUnit_of_mul_isUnit_left this

theorem gs_eval_eq {Rg : Type} [CommRing Rg] {fB : B₀ ⟶ Sp Rg} {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H}
    {φ : X ⟶ A₀} {p : X ⟶ T} {c : Fin mA → Fin mB → Γ(T, ⊤)} {Ψ₁ Ψ₂ : X ⟶ B₀}
    (hcov : ⨆ i, nonzeroLocus (b i) = ⊤) (hH : H.IsLB) (hN : N.IsLB) (hG : Generates a φ p c)
    (h₁ : Proport a b φ p Ψ₁ c) (h₂ : Proport a b φ p Ψ₂ c) (e : Ψ₁ ≫ fB = Ψ₂ ≫ fB) {i : Fin mB}
    {r : Fin mB → Γ(B₀, nonzeroLocus (b i))} (hr : ∀ j, GlobalTheory.AmpleSpan.IsRatio (b j) (b i) (r j)) (x : X)
    (m₁ : Ψ₁ x ∈ nonzeroLocus (b i)) (m₂ : Ψ₂ x ∈ nonzeroLocus (b i)) (P : MvPolynomial (Fin mB) Γ(Sp Rg, ⊤)) :
    gs Ψ₁ x _ (MvPolynomial.eval₂Hom (fB.appLE ⊤ (nonzeroLocus (b i)) le_top).hom r P) =
      gs Ψ₂ x _ (MvPolynomial.eval₂Hom (fB.appLE ⊤ (nonzeroLocus (b i)) le_top).hom r P) := by
  obtain ⟨q, hq⟩ := exists_chart hN (φ x)
  have key : ∀ Ψ : X ⟶ B₀, Proport a b φ p Ψ c → Ψ x ∈ nonzeroLocus (b i) → ∀ j,
      gs Ψ x _ (r j) * comb a φ p c x q i = comb a φ p c x q j := fun Ψ hP m j => by
    obtain ⟨k, hk⟩ := exists_chart hH (Ψ x)
    have ub := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i) Ψ x hk).1 m
    have e₁ := hP x q k hq hk j i
    rw [(hr j).gs Ψ x m hk] at e₁
    refine ub.mul_left_cancel ?_
    rw [← e₁]
    ring
  have uc : IsUnit (comb a φ p c x q i) := by
    obtain ⟨k, hk⟩ := exists_chart hH (Ψ₁ x)
    exact (mem_nonzeroLocus_iff_comb hcov hG h₁ hq hk i).1 m₁
  induction P using MvPolynomial.induction_on with
  | C a₀ =>
    rw [MvPolynomial.eval₂Hom_C, GlobalTheory.AmpleSpan.gs_const fB _ Ψ₁ x m₁, GlobalTheory.AmpleSpan.gs_const fB _ Ψ₂ x m₂, e]
  | add P Q hP hQ => rw [map_add (f := _), gs_add _ x _ m₁, gs_add _ x _ m₂, hP, hQ]
  | mul_X P j hP =>
    rw [map_mul, gs_mul _ x _ m₁, gs_mul _ x _ m₂, hP, MvPolynomial.eval₂Hom_X']
    exact congrArg _ (uc.mul_right_cancel ((key Ψ₁ h₁ m₁ j).trans (key Ψ₂ h₂ m₂ j).symm))

theorem eq_of_proport : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (Ψ₁ Ψ₂ : X ⟶ B₀), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → GlobalTheory.HomFixUniv.Generates a φ p c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₁ c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₂ c → Ψ₁ ≫ fB = Ψ₂ ≫ fB → Ψ₁ = Ψ₂ := by
  intro Rg _ A₀ B₀ X T fB N H mA mB a b φ p c Ψ₁ Ψ₂ hE hH hN hG h₁ h₂ e
  obtain ⟨hcov, hloc⟩ := hE
  have hW : ⨆ i, Ψ₁ ⁻¹ᵁ nonzeroLocus (b i) = ⊤ := by
    refine top_le_iff.1 fun x _ => Opens.mem_iSup.2 ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (Ψ₁ x)))
    exact ⟨i, hi⟩
  let 𝒰 := X.openCoverOfIsOpenCover (fun i => Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)) hW
  refine 𝒰.hom_ext _ _ fun i => ?_
  obtain ⟨ha, r, hr, hs⟩ := hloc i
  have m₂ : ∀ x, Ψ₁ x ∈ nonzeroLocus (b i) → Ψ₂ x ∈ nonzeroLocus (b i) := fun x hx => by
    obtain ⟨q, hq⟩ := exists_chart hN (φ x)
    obtain ⟨k₁, hk₁⟩ := exists_chart hH (Ψ₁ x)
    obtain ⟨k₂, hk₂⟩ := exists_chart hH (Ψ₂ x)
    exact (mem_nonzeroLocus_iff_comb hcov hG h₂ hq hk₂ i).2 ((mem_nonzeroLocus_iff_comb hcov hG h₁ hq hk₁ i).1 hx)
  change (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι ≫ Ψ₁ = (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι ≫ Ψ₂
  have w₁ : ∀ w : (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).toScheme, Ψ₁ ((Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι w) ∈ nonzeroLocus (b i) :=
    fun w => w.2
  refine GlobalTheory.SecRingIso.hom_ext_affine ha (fun w => w₁ w) (fun w => m₂ _ (w₁ w)) fun f w => ?_
  obtain ⟨P, rfl⟩ := hs f
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_comp _ Ψ₁ w _ (w₁ w), ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_comp _ Ψ₂ w _ (m₂ _ (w₁ w))]
  exact congrArg _ (gs_eval_eq hcov hH hN hG h₁ h₂ e hr _ (w₁ w) (m₂ _ (w₁ w)) P)

end GlobalTheory.HomFixUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceOfStrictlyHenselianSta
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LocGlob

variable {S : Scheme.{0}} {ι : Type} (V : ι → Over S)

def cop : Over S := Over.mk (Sigma.desc fun i => (V i).hom)

def cι (i : ι) : V i ⟶ cop V := Over.homMk (Sigma.ι (fun i => (V i).left) i) (by simp [cop])

def cdesc {U : Over S} (h : ∀ i, V i ⟶ U) : cop V ⟶ U :=
  Over.homMk (Sigma.desc fun i => (h i).left) (by
    apply Sigma.hom_ext
    intro i
    simp [cop])

theorem cι_cdesc {U : Over S} (h : ∀ i, V i ⟶ U) (i : ι) : cι V i ≫ cdesc V h = h i := by
  ext1
  change Sigma.ι (fun i => (V i).left) i ≫ Sigma.desc (fun i => (h i).left) = (h i).left
  exact Sigma.ι_desc _ _

def cop_isColimit : IsColimit (Cofan.mk (cop V).left (fun i => (cι V i).left)) :=
  coproductIsCoproduct _

theorem cop_etale (hV : ∀ i, Etale (V i).hom) : Etale (cop V).hom := by
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hV

end GlobalTheory.EtC.LocGlob

open GlobalTheory.EtC.LocGlob in
theorem GlobalTheory.EtC.loc_glob_classes : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → ∀ (U : Over S), Etale U.hom → ∀ n : ℤ, (∀ x : H R ((bc (α ≫ p)).obj U) F n, ∃ (V : Over S) (h : V ⟶ U) (y : H R ((bc p).obj V) F n), Etale V.hom ∧ Surjective h.left ∧ pull R ((bcMap α p).app V) F n y = pull R ((bc (α ≫ p)).map h) F n x) ∧ ∀ y : H R ((bc p).obj U) F n, pull R ((bcMap α p).app U) F n y = 0 → ∃ (V : Over S) (h : V ⟶ U), Etale V.hom ∧ Surjective h.left ∧ pull R ((bc p).map h) F n y = 0 := by
  intro R _ F S E E' α p hF hq1 hq2 hEqv U hU n
  have cont1 := GlobalTheory.T.finitarySheaf_continuous_baseChange_levelwiseQcqs R F hF S E (α ≫ p) hq1
  have cont2 := GlobalTheory.T.finitarySheaf_continuous_baseChange_levelwiseQcqs R F hF S E' p hq2
  choose O instO s g hs v hv using GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point S U hU
  have loc := fun u => @GlobalTheory.T.etaleSpaceCohomology_stalk_local_classes R _ F S _ _ (bcMap α p) cont1 cont2 (O u) (instO u) (s u) (hs u)
    (@hEqv (O u) (instO u) (s u) (hs u)) U hU (g u) n
  have surjOf : ∀ (V : U.left → Over S) (g' : ∀ u, Over.mk (s u) ⟶ V u) (h : ∀ u, V u ⟶ U),
      (∀ u, g' u ≫ h u = g u) → Surjective (cdesc V h).left := by
    intro V g' h hg
    refine ⟨fun u0 => ⟨((g' u0 ≫ cι V u0).left) (v u0), ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, cι_cdesc, hg, hv]
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · choose V g' h y hV hg hy using fun u => (loc u).1 x
    obtain ⟨Y, hY⟩ := (GlobalTheory.T.etaleSpaceCohomology_baseChange_coprod_bijective R F S E' p (cop V) U.left V (cι V) (cop_isColimit V) n).2 y
    refine ⟨cop V, cdesc V h, Y, cop_etale V hV, surjOf V g' h hg, ?_⟩
    apply (GlobalTheory.T.etaleSpaceCohomology_baseChange_coprod_bijective R F S E (α ≫ p) (cop V) U.left V (cι V) (cop_isColimit V) n).1
    funext u
    simp only
    have hYu : pull R ((bc p).map (cι V u)) F n Y = y u := congrFun hY u
    rw [← pull_comp, ← pull_comp, (bcMap α p).naturality, ← Functor.map_comp, cι_cdesc, pull_comp,
      hYu, hy u]
  · choose V g' h hV hg hy0 using fun u => (loc u).2 y hy
    refine ⟨cop V, cdesc V h, cop_etale V hV, surjOf V g' h hg, ?_⟩
    apply (GlobalTheory.T.etaleSpaceCohomology_baseChange_coprod_bijective R F S E' p (cop V) U.left V (cι V) (cop_isColimit V) n).1
    funext u
    simp only [map_zero]
    rw [← pull_comp, ← Functor.map_comp, cι_cdesc, hy0 u]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyVanishingAlgebraicOverRatFunc
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CdOne

open GroundTheory.ProfCoh

theorem subsingleton_cohomology_trivial_zmod (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (q : ℕ) [NeZero q]
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q → cdp ℓ G ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (cohomology (Rep.trivial (ZMod q) G (ZMod q)) n) := by
  let A : Rep.{0} (ULift.{0} ℤ) G := Rep.trivial (ULift.{0} ℤ) G (ULift.{0} (ZMod q))
  have hq0 : q ≠ 0 := NeZero.ne q
  have hA : ∀ a : A, q • a = 0 := fun a => by
    change (q • a : ULift.{0} (ZMod q)) = 0
    ext
    simp
  have htors : IsAddTorsion A := fun a =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q, Nat.pos_of_ne_zero hq0, hA a⟩
  have hsub : Subsingleton (cohomology A n) := by
    suffices h' : ∀ x : cohomology A n, x = 0 from ⟨fun x y => (h' x).trans (h' y).symm⟩
    intro x
    refine eq_zero_of_primaryComponent_eq_bot q hq0 (fun ℓ hℓ hℓq => ?_) x
      (nsmul_cohomology_eq_zero A hA n x)
    refine primaryComponent_cohomology_eq_bot_of_cdp_lt (p := ℓ) A htors ?_
    calc cdp ℓ G ≤ 1 := h ℓ hℓ hℓq
      _ < n := by exact_mod_cast (show 1 < n by omega)
  let e : A ≃+ (Rep.trivial (ZMod q) G (ZMod q) : Rep (ZMod q) G) := AddEquiv.ulift
  exact (cohomologyAddEquivOfEquiv (A := A) (A' := Rep.trivial (ZMod q) G (ZMod q)) e
    (fun _ _ => rfl) n).symm.injective.subsingleton

end GlobalTheory.EtC.CdOne

namespace GlobalTheory.EtC

theorem gaugeSplitting_holds : C1 := by
  intro q _ k K _ _ _ _ _ hq n i hn
  let f : k →+* K := (algebraMap (RatFunc k) K).comp (algebraMap k (RatFunc k))
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqk : (q : k) ≠ 0 := by
    intro h0
    have : (q : K) = 0 := by rw [← map_natCast f q, h0, map_zero]
    exact hq.ne_zero this
  haveI : NeZero (q : k) := ⟨hqk⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (Polynomial.degree_cyclotomic_pos q k hq0).ne'
  have hζk : IsPrimitiveRoot ζ q := (Polynomial.isRoot_cyclotomic_iff).1 hζ
  have hζK : IsPrimitiveRoot (f ζ) q := hζk.map_of_injective f.injective
  have hroot : ∃ z : K, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
    refine ⟨f ζ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζK.isRoot_cyclotomic hq0
  obtain ⟨u⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q K hq hroot n i 0
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by omega)
  have hm : 2 ≤ m := by omega
  let Ω := SeparableClosure K
  have hζΩ : IsPrimitiveRoot (algebraMap K Ω (f ζ)) q :=
    hζK.map_of_injective (algebraMap K Ω).injective
  obtain ⟨e⟩ := GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology q K Ω hq 0 (Rep.trivial (ZMod q) (Ω ≃ₐ[K] Ω) (ZMod q)) _ hζΩ
    (Module.Basis.singleton Unit (ZMod q)) (fun σ a _ => by simp) m
  have hsub := GlobalTheory.EtC.CdOne.subsingleton_cohomology_trivial_zmod (Ω ≃ₐ[K] Ω) q
    (fun ℓ hℓ _ => GlobalTheory.T.cdp_galois_le_one_of_isAlgebraic_ratFunc k K Ω ℓ hℓ) m hm
  exact (u.trans e).injective.subsingleton

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockGroupUnipotentDoubleCosetCellBlockDia
section
open Matrix Topology

noncomputable section

namespace GlobalTheory.JSW.Cut.Block

open GlobalTheory.JSW.KirFin GlobalTheory.SmGL

variable {F : Type} [NormedField F] {m : ℕ}

open Matrix Topology in
variable {F : Type} [NormedField F] {m : ℕ} in
theorem _root_.GlobalTheory.JSW.Cut.Block.mir_inv (a : GL (Fin m) F) (y : Fin m → F) :
    (_root_.GlobalTheory.JSW.KirFin.mir a y)⁻¹ =
      _root_.GlobalTheory.JSW.KirFin.mir a⁻¹ (-((a⁻¹).val *ᵥ y)) := by
  apply inv_eq_of_mul_eq_one_right
  rw [_root_.GlobalTheory.JSW.KirFin.mir_mul]
  simp [mulVec_neg, mulVec_mulVec, ← _root_.GlobalTheory.JSW.KirFin.mir_one]

theorem mir_left_inj {g h : GL (Fin m) F} {x y : Fin m → F} (e : mir g x = mir h y) : g = h := by
  ext i j
  have := congrArg (fun p : GL (Fin (m + 1)) F => p.val i.castSucc j.castSucc) e
  simpa using this

def blocks (U : Subgroup (GL (Fin (m + 1)) F)) : Subgroup (GL (Fin m) F) where
  carrier := {a | ∃ y, mir a y ∈ U}
  one_mem' := ⟨0, by rw [mir_one]; exact U.one_mem⟩
  mul_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨a.val *ᵥ z + y, by rw [← mir_mul]; exact U.mul_mem hy hz⟩
  inv_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨_, by rw [← mir_inv]; exact U.inv_mem hy⟩

theorem exists_blocks_cell_cor_iff : ∀ {F : Type} [NormedField F] {m : ℕ} (U : Subgroup (GL (Fin (m + 2)) F)), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∃ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) ∧ IsOpen (B : Set (GL (Fin (m + 1)) F)) ∧ (∀ b, GlobalTheory.JSW.KirFin.cor b ∈ U → b ∈ B) ∧ ∀ h₀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.cor h ∈ GlobalTheory.JSW.Cut.cell (GlobalTheory.JSW.KirFin.cor h₀) (U : Set (GL (Fin (m + 2)) F)) ↔ h ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
  intro F _ m U hUc hUo
  refine ⟨blocks U, isCompact_blocks hUc, ?_, fun b hb => ⟨0, hb⟩, fun h₀ h => ?_⟩
  · exact Subgroup.isOpen_mono (H₁ := U.comap cor) (fun b hb => ⟨0, hb⟩) (hUo.preimage continuous_cor)
  constructor
  · rintro ⟨n, hn, u, hu, e⟩
    obtain ⟨n', x, rfl⟩ := exists_mir (lr_of_mem hn)
    have hlu : lr u = lr 1 := by
      have h1 : lr (cor h) = lr (1 * u) := by
        rw [e]
        refine lr_mul_congr ?_ u
        rw [lr_mul_congr (lr_of_mem hn) _, one_mul]
        exact lr_mir h₀ 0
      rw [one_mul] at h1
      rw [← h1]
      exact lr_mir h 0
    obtain ⟨a, y, rfl⟩ := exists_mir hlu
    refine ⟨n', mir_mem_iff.1 hn, a, ⟨y, hu⟩, ?_⟩
    change mir h 0 = mir n' x * mir h₀ 0 * mir a y at e
    rw [mir_mul, mir_mul] at e
    exact mir_left_inj e
  · rintro ⟨n', hn', a, ⟨y, hy⟩, rfl⟩
    refine ⟨mir n' (-((n' * h₀).val *ᵥ y)), mir_mem_iff.2 hn', mir a y, hy, ?_⟩
    change mir (n' * h₀ * a) 0 = mir n' _ * mir h₀ 0 * mir a y
    rw [mir_mul, mir_mul, mulVec_zero, zero_add, add_neg_cancel]

end GlobalTheory.JSW.Cut.Block
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdAllAway
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.InertRank

theorem exists_dvd_all {A ι : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    (a : ι → A) (s : Finset ι) (h : ∃ i ∈ s, a i ≠ 0) :
    ∃ j ∈ s, a j ≠ 0 ∧ ∀ i ∈ s, a j ∣ a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at h
  | insert k s _ ih =>
    by_cases hs : ∃ i ∈ s, a i ≠ 0
    · obtain ⟨j, hj, hj0, hdvd⟩ := ih hs
      rcases ValuationRing.dvd_total (a j) (a k) with hjk | hkj
      · refine ⟨j, Finset.mem_insert_of_mem hj, hj0, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hjk
        · exact hdvd i hi
      · refine ⟨k, Finset.mem_insert_self _ _, fun h0 => hj0 ?_, fun i hi => ?_⟩
        · rw [h0] at hkj
          exact zero_dvd_iff.1 hkj
        · rcases Finset.mem_insert.1 hi with rfl | hi
          · exact dvd_rfl
          · exact hkj.trans (hdvd i hi)
    · push_neg at hs
      obtain ⟨i, hi, hi0⟩ := h
      have hk : a k ≠ 0 := by
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hi0
        · exact absurd (hs i hi) hi0
      refine ⟨k, Finset.mem_insert_self _ _, hk, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact dvd_rfl
      · rw [hs i hi]
        exact dvd_zero _

theorem exists_dvd_all_away {R ι : Type*} [CommRing R] [IsDedekindDomain R] [Fintype ι]
    (P : HeightOneSpectrum R) (a : ι → R) (h : ∃ i, a i ≠ 0) :
    ∃ j, a j ≠ 0 ∧ ∀ i, ∃ r s : R, s ∉ P.asIdeal ∧ s * a i = a j * r := by
  let A := Localization.AtPrime P.asIdeal
  have hinj : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A (Ideal.primeCompl_le_nonZeroDivisors P.asIdeal)
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot A
  obtain ⟨i0, hi0⟩ := h
  obtain ⟨j, -, hj0, hdvd⟩ := exists_dvd_all (fun i => algebraMap R A (a i)) Finset.univ
    ⟨i0, Finset.mem_univ _, fun h0 => hi0 (hinj (by simpa using h0))⟩
  refine ⟨j, fun h0 => hj0 (by simp [h0]), fun i => ?_⟩
  obtain ⟨c, hc⟩ := hdvd i (Finset.mem_univ _)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.asIdeal.primeCompl c
  refine ⟨r, (s : R), s.2, hinj ?_⟩
  have hs := IsLocalization.mk'_spec A r s
  simp only at hc
  rw [map_mul, map_mul, hc, ← hs]
  ring

theorem exists_dep_away {E : Type} [Field E] [NumberField E] {n : ℕ} {ι : Type} [Fintype ι]
    (P : HeightOneSpectrum (𝓞 E)) (v : ι → Fin n → E) (hcard : n < Fintype.card ι) :
    ∃ b : ι → 𝓞 E, ∑ i, b i • v i = 0 ∧ ∃ j, b j ∉ P.asIdeal := by
  classical
  have hdep : ¬ LinearIndependent (𝓞 E) v := by
    intro hli
    have := (LinearIndependent.iff_fractionRing (𝓞 E) E).1 hli |>.fintype_card_le_finrank
    simp at this
    omega
  obtain ⟨a, ha, hne⟩ := Fintype.not_linearIndependent_iff.1 hdep
  obtain ⟨j, hj0, hall⟩ := exists_dvd_all_away P a hne
  choose r s hs hrs using hall
  refine ⟨fun i => (∏ k ∈ Finset.univ.erase i, s k) * r i, ?_, j, ?_⟩
  · have hcoef : ∀ i, a j * ((∏ k ∈ Finset.univ.erase i, s k) * r i) = (∏ k, s k) * a i := by
      intro i
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)]
      linear_combination (-(∏ k ∈ Finset.univ.erase i, s k)) * hrs i
    have h1 : a j • ∑ i, ((∏ k ∈ Finset.univ.erase i, s k) * r i) • v i = 0 := by
      rw [Finset.smul_sum]
      simp_rw [smul_smul, hcoef, mul_smul]
      rw [← Finset.smul_sum, ha, smul_zero]
    have hj0' : algebraMap (𝓞 E) E (a j) ≠ 0 := by simpa using hj0
    have h2 : algebraMap (𝓞 E) E (a j) • ∑ i, ((∏ k ∈ Finset.univ.erase i, s k) * r i) • v i = 0 := by
      rw [algebraMap_smul]; exact h1
    exact (smul_eq_zero.1 h2).resolve_left hj0'
  · have hsj : r j = s j := by
      have : a j * r j = a j * s j := by rw [← hrs j, mul_comm]
      exact mul_left_cancel₀ hj0 this
    beta_reduce
    rw [hsj, mul_comm, Finset.mul_prod_erase Finset.univ s (Finset.mem_univ j)]
    intro hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hmem
    exact hs k hk

theorem coeff_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {P : Ideal (𝓞 E)} {y : List ℕ}
    (hy : ∀ a ∈ y, 0 < a) (A B : Submodule (𝓞 E) (Formalism.L2.Col.Sp E n))
    (e : (A ⧸ (B ⊓ A).comap A.subtype) ≃ₗ[𝓞 E] Formalism.L2.Col.inType P y)
    (x : Fin y.length → A)
    (hx : ∀ i, e (Submodule.Quotient.mk (x i)) = Pi.single i 1)
    (b : Fin y.length → 𝓞 E) (hz : (∑ i, b i • (x i : Formalism.L2.Col.Sp E n)) ∈ B)
    (i : Fin y.length) : b i ∈ P := by
  classical
  have hq : (Submodule.Quotient.mk (∑ k, b k • x k) : A ⧸ (B ⊓ A).comap A.subtype) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    refine ⟨?_, (∑ k, b k • x k).2⟩
    simpa using hz
  have he : (∑ k, b k • (Pi.single k 1 : Formalism.L2.Col.inType P y)) = 0 := by
    have := congrArg e hq
    rw [e.map_zero] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, ← Submodule.mkQ_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, e.map_smul, Submodule.mkQ_apply, hx]
  have hi := congrFun he i
  rw [Finset.sum_apply, Finset.sum_eq_single i
    (fun k _ hk => by rw [Pi.smul_apply, Pi.single_eq_of_ne hk.symm, smul_zero]) (by simp),
    Pi.smul_apply, Pi.single_eq_same] at hi
  have hi' : (Ideal.Quotient.mk (P ^ y.get i)) (b i) = 0 := by
    simpa [Algebra.smul_def] using hi
  have hmem := Ideal.Quotient.eq_zero_iff_mem.1 hi'
  have hpos : 0 < y.get i := hy _ (List.get_mem y i)
  exact Ideal.pow_le_self hpos.ne' hmem

theorem two_mul_length_le {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (P : HeightOneSpectrum (𝓞 E)) (y : List ℕ)
    (d e : Col.DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (hy : ∀ a ∈ y, 0 < a) (he : e ∈ d.inertSet P.asIdeal y) :
    2 * y.length ≤ n := by
  classical
  obtain ⟨⟨⟨e1⟩, ⟨e2⟩⟩, -, -⟩ := he
  by_contra hlt
  have lift : ∀ {A B : Submodule (𝓞 E) (Formalism.L2.Col.Sp E n)}
      (f : (A ⧸ (B ⊓ A).comap A.subtype) ≃ₗ[𝓞 E] Formalism.L2.Col.inType P.asIdeal y),
      ∃ x : Fin y.length → A, ∀ i, f (Submodule.Quotient.mk (x i)) = Pi.single i 1 := by
    intro A B f
    have : ∀ i, ∃ a : A, f (Submodule.Quotient.mk a) = Pi.single i 1 := fun i => by
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (f.symm (Pi.single i 1))
      exact ⟨a, by rw [ha, LinearEquiv.apply_symm_apply]⟩
    choose x hx using this
    exact ⟨x, hx⟩
  obtain ⟨x, hx⟩ := lift e1
  obtain ⟨x', hx'⟩ := lift e2
  obtain ⟨b, hb, j, hj⟩ := exists_dep_away (ι := Fin y.length ⊕ Fin y.length) P
    (Sum.elim (fun i => (x i : Formalism.L2.Col.Sp E n)) (fun i => (x' i : Formalism.L2.Col.Sp E n)))
    (by simp; omega)
  rw [Fintype.sum_sum_type] at hb
  simp only [Sum.elim_inl, Sum.elim_inr] at hb
  have h1 : (∑ i, b (Sum.inl i) • (x i : Formalism.L2.Col.Sp E n)) ∈ e.1.N := by
    rw [eq_neg_of_add_eq_zero_left hb]
    exact neg_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (x' i).2)
  have h2 : (∑ i, b (Sum.inr i) • (x' i : Formalism.L2.Col.Sp E n)) ∈ d.1.N := by
    rw [eq_neg_of_add_eq_zero_right hb]
    exact neg_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (x i).2)
  rcases j with j | j
  · exact hj (coeff_mem hy _ _ e1 x hx (fun i => b (Sum.inl i)) h1 j)
  · exact hj (coeff_mem hy _ _ e2 x' hx' (fun i => b (Sum.inr i)) h2 j)

end GlobalTheory.InertRank
end

