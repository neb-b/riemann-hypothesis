module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualOneFormsInvariantFieldsAffineOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.GcDual

def cHom {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (W : X.Opens) : K →+* Γ(X, W) :=
  (p.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem coeffs_zero {K : Type} [Field K] (P₀ : Out.PolAV (Sp K)) (n : ℕ)
    (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left)
    (hd : ∀ a, IsInv P₀.A (v a) (dd a)) (W : P₀.A.left.Opens) (hW : IsAffineOpen W)
    {C : Type} [CommRing C] (ψ : Γ(P₀.A.left, W) →+* C) (c : Fin n → C)
    (hc : ∀ f, ∑ a, c a * ψ (dd a W f) = 0) : c = 0 := by
  haveI := P₀.smoothDim
  haveI : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g _
  letI : Algebra K C := (ψ.comp (cHom P₀.A.hom W)).toAlgebra
  obtain ⟨x, hx, ex⟩ := exists_evalPt_eq hW ψ
  have hxp : x ≫ P₀.A.hom = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) C).hom := by
    refine (eq_spMap_of_evalPt _ (algebraMap K C) fun a => ?_).trans rfl
    rw [← evalPt_constFn P₀.A.hom x W hx, ex]
    rfl
  let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) C ⟶ P₀.A := Over.homMk x hxp
  obtain ⟨c₀, -, hu⟩ := GlobalTheory.VertCoeffRing.existsUnique_coeff_alg (GlobalTheory.VertCoeffRing.isLieBasis_tvE v)
    (fun B _ _ e he z O h => GlobalTheory.VertCoeffRing.evalPt_lieExp v dd hd B e he z O h) y hW hx (fun _ => 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ => rfl)
  have h1 := hu c (fun f => by simpa [y, ex] using (hc f).symm)
  have h2 := hu 0 (fun f => by simp)
  rw [h1, h2]

end GlobalTheory.GcDual

namespace GlobalTheory.GcDual

variable {A : Type} [CommRing A] {n : ℕ}

theorem mem_smul_top_of_forall_mem (I : Ideal A) (x : Fin n → A) (hx : ∀ b, x b ∈ I) :
    x ∈ I • (⊤ : Submodule A (Fin n → A)) := by
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun b _ => ?_
  have : Pi.single b (x b) = x b • (Pi.single b 1 : Fin n → A) := by
    rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (hx b) trivial

theorem eq_top_of_forall_maximal (M : Submodule A (Fin n → A))
    (h : ∀ m : Ideal A, m.IsMaximal → ∀ x, x ∈ M ⊔ m • (⊤ : Submodule A (Fin n → A))) : M = ⊤ := by
  have hQ : ∀ m : Ideal A, m.IsMaximal → ∃ r : A, r - 1 ∈ m ∧ ∀ q : (Fin n → A) ⧸ M, r • q = 0 := by
    intro m hm
    have hle : (⊤ : Submodule A ((Fin n → A) ⧸ M)) ≤ m • ⊤ := by
      intro q _
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective M q
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h m hm x)
      have hz' : M.mkQ z ∈ m • (⊤ : Submodule A ((Fin n → A) ⧸ M)) := by
        have : m • (⊤ : Submodule A (Fin n → A)) ≤ (m • (⊤ : Submodule A ((Fin n → A) ⧸ M))).comap M.mkQ :=
          Submodule.smul_le.2 fun r hr t _ => by
            rw [Submodule.mem_comap, map_smul]
            exact Submodule.smul_mem_smul hr trivial
        exact this hz
      have e : Submodule.Quotient.mk (p := M) (y + z) = M.mkQ z := by
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero M).2 hy, zero_add]; rfl
      rw [e]; exact hz'
    obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
      (Module.Finite.fg_top) hle
    exact ⟨r, hr, fun q => hr' q trivial⟩
  have h1 : ∀ q : (Fin n → A) ⧸ M, q = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨q₀, hq₀⟩ := hne
    let I : Ideal A := Module.annihilator A ((Fin n → A) ⧸ M)
    have hI : I ≠ ⊤ := by
      intro hI
      have : (1 : A) ∈ I := hI ▸ Submodule.mem_top
      exact hq₀ (by simpa using Module.mem_annihilator.1 this q₀)
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨r, hr, hr'⟩ := hQ m hm
    have hrI : r ∈ I := Module.mem_annihilator.2 hr'
    have : (1 : A) ∈ m := by
      have := m.sub_mem (hIm hrI) hr
      simpa using this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 this)
  rw [eq_top_iff]
  intro x _
  exact (Submodule.Quotient.mk_eq_zero M).1 (h1 _)

end GlobalTheory.GcDual

namespace GlobalTheory.GcDual

theorem span_eq_top {K : Type} [Field K] (P₀ : Out.PolAV (Sp K)) (n : ℕ)
    (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left)
    (hd : ∀ a, IsInv P₀.A (v a) (dd a)) (W : P₀.A.left.Opens) (hW : IsAffineOpen W) :
    Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) = ⊤ := by
  set M := Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) with hM
  refine eq_top_of_forall_maximal M fun m hm x => ?_
  haveI := hm
  letI : Field (Γ(P₀.A.left, W) ⧸ m) := Ideal.Quotient.field m
  let π : Γ(P₀.A.left, W) →+* Γ(P₀.A.left, W) ⧸ m := Ideal.Quotient.mk m
  let S : Submodule (Γ(P₀.A.left, W) ⧸ m) (Fin n → Γ(P₀.A.left, W) ⧸ m) :=
    Submodule.span _ (Set.range fun f : Γ(P₀.A.left, W) => fun b => π (dd b W f))
  have hS : S = ⊤ := by
    by_contra hS
    obtain ⟨φ, hφ0, hφ⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hS)
    classical
    let c : Fin n → Γ(P₀.A.left, W) ⧸ m := fun b => φ fun j => if b = j then 1 else 0
    have hc := coeffs_zero P₀ n v dd hd W hW π c fun f => by
      have := hφ (Submodule.subset_span ⟨f, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at this
      simpa [c, smul_eq_mul, mul_comm] using this
    apply hφ0
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    have : ∀ i, φ (fun j => if i = j then 1 else 0) = 0 := fun i => congrFun hc i
    simp [this]
  have lift : ∀ y ∈ S, ∃ x₀ ∈ M, (fun b => π (x₀ b)) = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, rfl⟩ := hy
      exact ⟨fun b => dd b W f, Submodule.subset_span ⟨f, rfl⟩, rfl⟩
    | zero => exact ⟨0, M.zero_mem, by ext; simp⟩
    | add y y' _ _ h h' =>
      obtain ⟨x₀, hx₀, rfl⟩ := h
      obtain ⟨x₁, hx₁, rfl⟩ := h'
      exact ⟨x₀ + x₁, M.add_mem hx₀ hx₁, by ext; simp⟩
    | smul s y _ h =>
      obtain ⟨x₀, hx₀, rfl⟩ := h
      obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s
      exact ⟨s' • x₀, M.smul_mem s' hx₀, by ext; simp [π]⟩
  obtain ⟨x₀, hx₀, e⟩ := lift (fun b => π (x b)) (hS ▸ Submodule.mem_top)
  have hk : x - x₀ ∈ m • (⊤ : Submodule Γ(P₀.A.left, W) (Fin n → Γ(P₀.A.left, W))) :=
    mem_smul_top_of_forall_mem m _ fun b => by
      rw [Pi.sub_apply, ← Ideal.Quotient.eq]
      exact (congrFun e b).symm
  have : x = x₀ + (x - x₀) := by abel
  rw [this]
  exact Submodule.add_mem_sup hx₀ hk

theorem exists_dual_forms : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ W : P₀.A.left.Opens, IsAffineOpen W → ∀ a : Fin n, ∃ (N : ℕ) (g f : Fin N → Γ(P₀.A.left, W)), ∀ b, ∑ i, g i * dd b W (f i) = if a = b then 1 else 0 := by
  intro K _ _ P₀ n v dd hd W hW a
  have hmem : (Pi.single a 1 : Fin n → Γ(P₀.A.left, W)) ∈
      Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) := by
    rw [span_eq_top P₀ n v dd hd W hW]; exact Submodule.mem_top
  obtain ⟨N, g, u, hu⟩ := Submodule.mem_span_set'.1 hmem
  refine ⟨N, g, fun i => (u i).2.choose, fun b => ?_⟩
  have h := congrFun hu b
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  have e : ∀ i, dd b W ((u i).2.choose) = (u i : Fin n → Γ(P₀.A.left, W)) b :=
    fun i => congrFun (u i).2.choose_spec b
  simp only [e]
  rw [h, Pi.single_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg (Ne.symm hab), if_neg hab]

end GlobalTheory.GcDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem bdParam_ne_zero (k : Type) [Field k] (m e : ℕ) (i : Fin m) : bdParam k m e i ≠ 0 := fun h => by
  have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin e) 1)) h
  simp [bdParam, MvPowerSeries.coeff_X] at this

theorem exists_fractionRing_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ∃ fK : FractionRing A →+* FractionRing B, spMap fK ≫ jK A = jK B ≫ spMap ψ := by
  have hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ) :=
    (IsFractionRing.injective B (FractionRing B)).comp hψ
  let fK : FractionRing A →+* FractionRing B :=
    IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg
  have e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x
  refine ⟨fK, ?_⟩
  have e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]
  have e2 := congrArg Spec.map e1
  rw [Spec.map_comp, Spec.map_comp] at e2
  exact e2

theorem exists_lift_normBl {X Z S : Scheme.{0}} (i : X ⟶ Z) (π : S ⟶ Z) (j : X ⟶ S) (J : Z.IdealSheafData)
    (hN : GlobalTheory.Poinc.IsNormBl π J) (hji : j ≫ π = i) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R] (a : Sp R ⟶ Z) (y : Sp (FractionRing R) ⟶ X) (hy : jK R ≫ a = y ≫ i) (f : R) (hf : f ≠ 0)
    (hJ : idlAlong J a = Ideal.span {f}) : ∃ ξ : Sp R ⟶ S, jK R ≫ ξ = y ≫ j := by
  obtain ⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩ := hN
  have hE : FinalTheorems.EffCartier (J.comap a) := GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J a f hf hJ
  have hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a)) := by
    refine GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf
    · rw [show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ,
        Ideal.map_span, Set.image_singleton]
  obtain ⟨b, hb, -⟩ := hB.2 _ a hE
  have hK : (y ≫ j) ≫ ν = jK R ≫ b := by
    refine (hB.2 _ _ hEK).unique ?_ ?_
    · rw [Category.assoc, Category.assoc, hνπ, hji, hy]
    · rw [Category.assoc, hb]
  obtain ⟨c, ⟨hc1, -⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK
  exact ⟨c, hc1⟩

theorem taut_exists_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∃ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT
  obtain ⟨hm, hs, -⟩ := hT
  have hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  haveI : CharZero k := (MvPowerSeries.C (σ := Fin m ⊕ Fin e) (R := k)).charZero
  have hAdm := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  have hBase : GlobalTheory.Mum.Base (ChartRing k m e) := ⟨hAdm, hcF⟩
  haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1
  obtain ⟨⟨-, -, hi, -, -, -, -⟩, -, hext, ⟨-, -, hval⟩, ⟨hbl, -, -, -, hji, -, -, -⟩, -⟩ := hU
  obtain ⟨ξZ, hξZ, -⟩ := hext _ hBase C.t ⟨C.P⟩ C.y C.gen (spMap C.b) C.y_over.symm
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) C.P.D.toPre.X
  have hPF := hpf C.P.D.toPre.X C.rank
  have hnat : ∀ i, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • C.δ i) = n := fun i =>
    hPF.exists_nat (Submodule.smul_mem _ _ (C.cone.mem i)) (fun y => by
      simpa using mul_nonneg (by positivity : (0 : ℤ) ≤ l.M') (C.cone.nonneg i y))
  choose b hb using hnat
  let a : Fin m → ℕ := fun i => d * b (Fin.cast hm.symm i)
  have hprod : ∏ i, bdParam k m e i ^ a i = ∏ i : Fin C.m, C.s i ^ (d * b i) :=
    (Fintype.prod_equiv (finCongr hm) _ _ (fun j => by simp [a, hs j])).symm
  have hI : idlAlong J ξZ = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
    refine GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr k m e _ a fun W _ _ _ hW ψ hψi hψl => ?_
    haveI := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hne : ∀ i, ψ (C.s i) ≠ 0 := fun i h0 => by
      have : C.s i = 0 := hψi (h0.trans (map_zero ψ).symm)
      rw [hs i] at this
      exact bdParam_ne_zero k m e _ this
    choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible (hne i) hϖ
    obtain ⟨fK, hκ⟩ := exists_fractionRing_map ψ hψi
    obtain ⟨t, tK, P, h1, h2, be, hbe, hmono, hφ⟩ :=
      _root_.GlobalTheory.UChart.pull_trait Xo c φ _ hBase C W hW ψ hψi hψl ϖ hϖ w hw (spMap fK) hκ
    obtain ⟨n, hn, hIn⟩ := hval W hW ϖ hϖ (spMap ψ ≫ ξZ) (spMap fK ≫ C.y)
      (by rw [Category.assoc, ← hξZ, ← Category.assoc, hκ, Category.assoc]) t tK h1 h2 P be hbe hmono
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hIn, hprod, map_prod]
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    have hnw : n = ∑ i, w i * (d * b i) := by
      have : (n : ℝ) = ∑ i, (w i : ℝ) * (d * b i) := by
        rw [hn, hφ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hb i]; ring
      exact_mod_cast this
    have : Associated (∏ i, ψ (C.s i ^ (d * b i))) (∏ i : Fin C.m, (ϖ ^ w i) ^ (d * b i)) :=
      Associated.prod _ _ _ fun i _ => by rw [map_pow]; exact (hw i).pow_pow
    rw [hnw]
    refine (this.trans ?_).symm
    rw [← Finset.prod_pow_eq_pow_sum]
    simp only [← pow_mul]
    exact Associated.refl _
  have hf0 : ∏ i, bdParam k m e i ^ a i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (bdParam_ne_zero k m e _)
  obtain ⟨ξ, hξ⟩ := exists_lift_normBl i π j J hbl hji _ ξZ C.y hξZ _ hf0 hI
  exact ⟨ξ, hξ.symm⟩

end GlobalTheory.UChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointClosureEqOfIsClopen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_genericPoint_closure_eq_of_isClopen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∃ η ∈ genericPoints (Xo.XF c), closure {C.i η} = A := by
  intro E _ _ _ H Dw _ l Xo c C A hA hirr hne
  obtain ⟨_, hyA, y, rfl⟩ := hne
  have hζ : IsGenericPoint hirr.genericPoint A := hirr.isGenericPoint_genericPoint hA.isClosed
  set ζ := hirr.genericPoint
  have h1 : ζ ⤳ C.i y := hζ.specializes hyA
  have hcomp : C.z (C.i y) = spMap C.b (pullback.snd C.z (spMap C.b) (C.iF y)) := by
    have := congrArg (fun f => f.base (C.iF y)) (pullback.condition (f := C.z) (g := spMap C.b))
    simpa using this
  have hbot : ∀ q : Sp c.F, (spMap C.b q).asIdeal = ⊥ := by
    intro q
    haveI := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
    show Ideal.comap C.b q.asIdeal = ⊥
    rw [hq]
    exact Ideal.comap_bot_of_injective C.b C.inj
  have h2 : C.z ζ = C.z (C.i y) := by
    have hs : C.z ζ ⤳ C.z (C.i y) := h1.map C.z.continuous
    have hle : (C.z ζ).asIdeal ≤ (C.z (C.i y)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 hs
    rw [hcomp, hbot] at hle
    apply PrimeSpectrum.ext
    rw [hcomp, hbot]
    exact le_bot_iff.1 hle
  obtain ⟨p', hp', -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.z) (g := spMap C.b) ζ
    (pullback.snd C.z (spMap C.b) (C.iF y)) (h2.trans hcomp)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := by
    letI := C.b.toAlgebra
    haveI := C.isFractionRing
    haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
    infer_instance
  have h3 : p' ⤳ C.iF y := by
    apply (IsPreimmersion.isEmbedding (pullback.fst C.z (spMap C.b))).specializes_iff.1
    rw [hp']
    exact h1
  haveI := C.iF_open
  obtain ⟨η, hη⟩ := h3.mem_open C.iF.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  have hCi : C.i η = ζ := by
    rw [← hp', ← hη]
    rfl
  have hinj : Function.Injective C.i := (IsPreimmersion.isEmbedding C.i).injective
  refine ⟨η, ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩, by rw [hCi]; exact hζ⟩
  have hη' : IsGenericPoint hT.closure.genericPoint (closure T) :=
    hT.closure.isGenericPoint_genericPoint isClosed_closure
  have hs : hT.closure.genericPoint ⤳ η := hη'.specializes (subset_closure (hle (subset_closure rfl)))
  have hs' : C.i hT.closure.genericPoint ⤳ ζ := hCi ▸ hs.map C.i.continuous
  have hmem : C.i hT.closure.genericPoint ∈ A := hs'.mem_open hA.isOpen hζ.mem
  have heq : hT.closure.genericPoint = η := hinj ((hs'.antisymm (hζ.specializes hmem)).eq.trans hCi.symm)
  rw [← heq, hη']
  exact subset_closure

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackMapSemiAbelianNormalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SemiAbDesc.exists_grpPullback_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {X S : Scheme.{0}} (j : X ⟶ S) (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G j e → ∀ (G₁ : Over (Sp R)) [GrpObj G₁], IsSemiAbelian G₁ → ∀ (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X), y ≫ j = jK R ≫ ξ → ∀ (B : Over (Sp (FractionRing R))) [GrpObj B] (a : B.left ⟶ G₁.left) (b : B.left ⟶ A.left), IsGrpPullback B G₁ (jK R) a → IsGrpPullback B A y b → ∃ πC : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ πC ∧ a ≫ πC = b ≫ e := by
  intro R _ _ _ _ X S j A _ G _ e hG hA G₁ _ hG₁ ξ y hyj B _ a b ha hb
  have hBG : IsGrpPullback B G (jK R ≫ ξ) (b ≫ e) := (hb.comp hA).congr hyj rfl
  have hG₂ : IsGrpPullback ((Over.pullback ξ).obj G) G ξ (pullback.fst G.hom ξ) := isGrpPullback_pullback G ξ
  have hsG₂ : IsSemiAbelian ((Over.pullback ξ).obj G) := IsSemiAbelian.pullback ξ G hG
  have hw : (b ≫ e) ≫ G.hom = (B.hom ≫ jK R) ≫ ξ := by rw [hBG.1.w, Category.assoc]
  let i₂ : B.left ⟶ ((Over.pullback ξ).obj G).left := pullback.lift (b ≫ e) (B.hom ≫ jK R) hw
  have hi₂ : i₂ ≫ pullback.fst G.hom ξ = b ≫ e := pullback.lift_fst _ _ _
  have hBG₂ : IsGrpPullback B ((Over.pullback ξ).obj G) (jK R) i₂ :=
    hG₂.cancel (hBG.congr rfl hi₂.symm) (pullback.lift_snd _ _ _)
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R) (ReciprocityTheory.ChartRestriction.G.Out.jK R) := .fractionField R (FractionRing R)
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G₁ hG₁
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hsG₂
  obtain ⟨E, ⟨hE, hEa⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) hj hG₁ hsG₂ ha hBG₂
  haveI := hE
  refine ⟨E.hom.left ≫ pullback.fst G.hom ξ, ((isGrpPullback_of_iso E).comp hG₂).congr (Category.id_comp _) rfl, ?_⟩
  rw [← Category.assoc, hEa, hi₂]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedLcCentreOfZeroLcThresholdStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isolated_lcCentre_of_zero_lcThreshold : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → 1 ≤ n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (x : X) (c : ℕ → ℝ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → N₀.IsLB → IsNef ℂ N₀ → IsBig ℂ N₀ →
      IsClosed ({x} : Set X) → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∑ e ∈ Finset.Icc 1 n, (e : ℝ) / c e ≤ 1 →
      ∀ (A : CartierDiv X) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X), IsAmpleLB (toLB A) → 0 < m' → D₀.Eff → 0 < μ →
        (lam : ℝ) < ∑ e ∈ Finset.Icc 1 n, (e : ℝ) / c e →
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) →
        LcCut p n (Δ + qWeil D₀ m') x 0 →
      ∃ (m : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m ∧ D₀.Eff ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C →
          (interNumRed ℂ C ![toLB D₀] : ℚ) / m = interNumRed ℂ C ![N₀] / r) ∧
        x ∈ U ∧ (∀ y ∈ U, LcAt p n (Δ + qWeil D₀ m) y) ∧
        (∀ y ∈ U, y ≠ x → KltAt p n (Δ + qWeil D₀ m) y) ∧ ¬ KltAt p n (Δ + qWeil D₀ m) x := by
  first | exact @GlobalTheory.PairStep.exists_isolated_of_lcCut_zero | exact GlobalTheory.PairStep.exists_isolated_of_lcCut_zero | (intros; apply GlobalTheory.PairStep.exists_isolated_of_lcCut_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionAtBoundaryPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BdStalkExt

theorem exists_extension_test {S X Y : Scheme.{0}} (g : X ⟶ S) [Smooth g] [QuasiCompact g] (e : Y ⟶ X)
    [IsOpenImmersion e] (x : S) [IsRegularLocalRing (S.presheaf.stalk x)] (L : LB Y) (hL : L.IsLB) :
    ∃ N : LB (pullback g (S.fromSpecStalk x)), N.IsLB ∧
      ∀ (T : Scheme.{0}) (a : T ⟶ pullback g (S.fromSpecStalk x)) (b : T ⟶ Y),
        a ≫ pullback.fst g (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b) := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.BdLocalExt.exists_extension_stalk g e x L hL
  refine ⟨N, hN, fun T a b hab => ?_⟩
  let t : T ⟶ pullback (e ≫ g) (S.fromSpecStalk x) :=
    pullback.lift b (a ≫ pullback.snd g (S.fromSpecStalk x)) (by
      rw [← Category.assoc, ← hab, Category.assoc, Category.assoc, pullback.condition])
  have ha : a = t ≫ pullback.map (e ≫ g) (S.fromSpecStalk x) g (S.fromSpecStalk x) e (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · rw [hab, Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have hb : b = t ≫ pullback.fst (e ≫ g) (S.fromSpecStalk x) := (pullback.lift_fst _ _ _).symm
  exact LBIso.chartPull (chartPullSame N _ _ _ t fun _ => ha) (chartPullSame L _ _ _ t fun _ => hb) h

theorem exists_extension_at_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ x : S, x ∉ Set.range j → ∃ N : LB (pullback G.hom (S.fromSpecStalk x)), N.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ pullback G.hom (S.fromSpecStalk x)) (b : T ⟶ tF.G.left), a ≫ pullback.fst G.hom (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (tF.PP.L.pull b) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU hpre tF _ G _ _ e hsa he _ x hx
  obtain ⟨-, -, -, -, ⟨-, hproj, -⟩, -⟩ := hU
  haveI := hsa.smooth
  haveI := hsa.quasiCompact
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  obtain ⟨k, _, m, n, C, ξ, a, -, -, rfl, het, -⟩ := hpre x hx
  haveI : IsRegularLocalRing (ChartRing k m n) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
  haveI : IsRegularLocalRing (S.presheaf.stalk (ξ (closedPoint _))) :=
    (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion _ het).1
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback (P := @IsOpenImmersion) he.1.flip inferInstance
  exact exists_extension_test G.hom e _ tF.PP.L tF.PP.isLB

end GlobalTheory.BdStalkExt
end
end

