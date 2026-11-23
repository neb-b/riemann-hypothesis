module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2928
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0660

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGridDatumPureTensorVacuaAE
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SmallDatumVac

theorem exists_datum_pure_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB ∧
      ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F v) → ℂ)
        (φ₀ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ),
        ΦB = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) ∧
        (∀ k, φ k Bs.v₁ = φ₀) ∧ φ₀ ∈ GlobalTheory.WeilM.SB _ ∧ φ₀ ≠ 0 ∧
        ∃ (L₁ : Submodule (𝓞 D.host.E) (Fin (G.V (.grid i j)).rank → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → D.host.E))
          (θ : 𝓞 D.host.E), (θ : D.host.E) + D.sp.cm.sig θ = 1 ∧ (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)) ∧
          ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀ := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  obtain ⟨ΦB, hD, m, f, φ, φ₀, hsum, hSB, hvac, hv1, h0SB, h0ne, L₁, L₂, θ, hL1, hL2, hSD, hθ, hfix⟩ :=
    GlobalTheory.T.exists_pureTensorSum_datum_routeThroughSmallVertex hL W B ρ t i j M hM Θ Θ' hΘ e Bs Γ X om om' h hTr hv
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr Bs.ψ Bs.v₁ := h.ψ ▸ GlobalTheory.T.localAddCharUnramified_of_splitsCompletelyAbovePlace W Bs.v₁ hTr.chars.good.2
  exact ⟨ΦB, hD, m, f, φ, φ₀, hsum, hSB, hvac, hv1, h0SB, h0ne, L₁, L₂, θ, hθ, hfix,
    fun ψ₀ hψ₀ hfix' => GlobalTheory.T.heisenbergLatticeVacuum_unique_up_to_scalar Bs Γ Bs.v₁ L₁ L₂ θ hψ hL1 hL2 hSD hθ φ₀ ψ₀ h0SB h0ne hfix hψ₀ hfix'⟩

end GlobalTheory.SmallDatumVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfPeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Build

lemma exp_nsmul {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (hadd : ∀ z w, e (z + w) = e z * e w) (z : Fin g → ℂ) : ∀ n : ℕ, e (n • z) = e z ^ n := by
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this |>.symm ▸ rfl
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

lemma exists_nsmul_eq_of_dvd {La : Type} [AddCommGroup La] (EF E₁ : LinearMap.BilinForm ℤ La) (hE₁ : EF = (2:ℤ) • E₁)
    (e₀ : ℕ) (a : La) (k : ℕ) (hdv : ∀ y, (k : ℤ) ∣ E₁ a y) (nondeg : ∀ x, (∀ y, EF x y = 0) → x = 0)
    (hperf : ∀ f : La →ₗ[ℤ] ℤ, ∃ x, E₁ x = e₀ • f) : ∃ x', e₀ • a = k • x' := by
  let φ : La →ₗ[ℤ] ℤ :=
    { toFun := fun y => E₁ a y / k
      map_add' := fun u v => by
        rw [map_add (f := _)]; exact Int.add_ediv_of_dvd_left (hdv u)
      map_smul' := fun c u => by
        rw [map_zsmul, smul_eq_mul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hdv u) }
  obtain ⟨x', hx''⟩ := hperf φ
  refine ⟨x', ?_⟩
  rw [← sub_eq_zero]
  apply nondeg
  intro y
  have hφ : E₁ x' y = e₀ * (E₁ a y / k) := by
    have := congrArg (fun F : La →ₗ[ℤ] ℤ => F y) hx''
    simpa [φ] using this
  have hm : (k : ℤ) * (E₁ a y / k) = E₁ a y := Int.mul_ediv_cancel' (hdv y)
  rw [hE₁]
  simp only [LinearMap.smul_apply, map_sub, map_nsmul, LinearMap.sub_apply, smul_eq_mul, nsmul_eq_mul, hφ]
  linear_combination (-2 * (e₀:ℤ)) * hm

lemma half_unique {La : Type} [AddCommGroup La] (E E' : LinearMap.BilinForm ℤ La) (h : (2:ℤ) • E = (2:ℤ) • E') :
    E = E' := by
  ext u v
  have h2 := congrArg (fun B : LinearMap.BilinForm ℤ La => B u v) h
  simp only [LinearMap.smul_apply, smul_eq_mul] at h2
  omega

end GlobalTheory.UPel.HT.Build


open GlobalTheory.UPel.HT.Build in
theorem GlobalTheory.UPel.HT.exists_obj_unifAt_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) t Q, 0 < N → N.Coprime p → b.IsType σ ρ → D.Cls N D' t → IsPeriod D' ρ Q → ∃ (o : Obj b N (spMap σ)) (h : _) (hL : _) (e : _), UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  intro p _ D R _ b N σ ρ D' t Q hN hNp htype hcls hper
  obtain ⟨hgen, E₁, hE₁, e₀, he₀p, hperf⟩ := hcls
  obtain ⟨A, _, _, act, P, e, hab, hdim, hP, r₁, r₂, hsy, ham, hexp, hker, hact, hweil⟩ :=
    _root_.GlobalTheory.HalvedPeriod.exists_abelian_of_isPeriod D.O D.inv D.g ρ D' Q E₁ hper hE₁
  have hadd := hexp.1
  have hsurj := hexp.2.1
  obtain ⟨hlie, hlieR⟩ := _root_.GlobalTheory.UPel.HT.lie_of_complexExp p D R b N σ ρ A act e hab hdim hexp hact htype
  have hgen' := hgen
  obtain ⟨f, ν, rfl, -, hf⟩ := hgen
  have hfN := hf N hN hNp
  let eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun a => e ((N : ℂ)⁻¹ • Q (f N a))
  have heta : ∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (f N a)) := fun a => Category.id_comp _
  have hsc : ∀ (c : D.O) (k : ℂ) (x : D'.La), e (k • Q (c • x)) = e (k • Q x) ≫ act.act c := by
    intro c k x
    rw [hper.1, ← Matrix.mulVec_smul, hact]
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hQ1 : ∀ x, e (Q x) = 1 := fun x => (hker _).2 ⟨x, rfl⟩
  have hgeom := _root_.GlobalTheory.UPel.HT.exists_tateIsoO_of_period p D N ρ A act _ D' (f N) Q e eta hN hNp hab (pull_isLB hP _) hgen' hper hadd hsurj hker
    hact hweil heta
  let o : Obj b N (spMap σ) :=
    { A := A
      ab := hab
      act := act
      P := P
      isLB := hP
      rig₁ := r₁
      rig₂ := r₂
      symm := hsy
      ample := ham
      kerP := ⟨e₀, he₀p, _root_.GlobalTheory.BiKill.kernel_pow_eq_one A D.g hab hdim P hP r₁ r₂ hsy ham e₀ (fun x hx => by
        obtain ⟨k, hk, hxk⟩ := _root_.GlobalTheory.KerPoincare.exists_pow_eq_one_of_kernel A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1
          hper.2.2.2.1 hker hweil x hx
        obtain ⟨z, rfl⟩ := hsurj x
        have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
        have h1 : e (k • z) = 1 := by rw [exp_nsmul e hadd]; exact hxk
        obtain ⟨a, ha⟩ := (hker _).1 h1
        have hz : z = (k : ℂ)⁻¹ • Q a := by
          rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul]
        obtain ⟨E₁', hE₁', hdiv⟩ := _root_.GlobalTheory.SymBirig.diag_form_two_smul_and_ker A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp
          hper.2.1 hker hweil
        have hx' : ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a))
            (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen := by
          rw [← hz]; exact hx
        have hdv : ∀ y, (k : ℤ) ∣ E₁' a y := (hdiv k a hk).2 hx'
        have hEE : E₁' = E₁ := half_unique _ _ (hE₁'.symm.trans hE₁)
        rw [hEE] at hdv
        obtain ⟨x', key⟩ := exists_nsmul_eq_of_dvd D'.EF E₁ hE₁ e₀ a k hdv D'.nondeg hperf
        have hQ : Q x' = e₀ • ((k : ℂ)⁻¹ • Q a) := by
          rw [smul_comm, ← map_nsmul, key, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk',
            one_smul]
        show e z ^ e₀ = 1
        rw [← exp_nsmul e hadd, hz, ← hQ]
        exact hQ1 x')⟩
      rosati := fun c => by
        refine (GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1 hker hweil
          (act.act c) (act.act (D.star c).unop) (AddMonoidHom.mk' (fun x => c • x) (smul_add c))
          (AddMonoidHom.mk' (fun x => (D.star c).unop • x) (smul_add _)) (act.hom c) (act.hom _)
          (fun k x _ => hsc c _ x) (fun k x _ => hsc _ _ x)).2 ?_
        intro x y
        exact D'.adj c x y
      lie := hlie
      lieRank := fun k _ _ x β hx i => hlieR k x β hx i
      eta := eta
      eta_add := fun x y => by
        show e _ = e _ * e _
        erw [map_add (f N) x y, map_add, smul_add, hadd]
        rfl
      eta_lin := fun c x => by
        obtain ⟨e', he'⟩ := hfN.2.1 c x
        show e _ = e _ ≫ _
        erw [he', map_add, smul_add, hadd, hsc, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1, _root_.mul_one]
      eta_ker := fun x => by
        show e _ = 1
        erw [map_nsmul (f N) N x, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1]
      geom := fun k _ _ x β _ => hgeom k x }
  refine ⟨o, hdim, pull_isLB hP _, e, ?_⟩
  refine ⟨Category.id_comp _, hper, hexp, hker, hact, hweil, heta⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatV
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

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatVAlg
open GlobalTheory.KS GlobalTheory.HeatGlue

variable {Y X : Scheme.{0}}

theorem pbT_id {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : pbT (𝟙 Y) s O = rsT s O := by
  rw [pbT_of_le (𝟙 Y) h, rsT_of_le h]
  rfl

theorem cst_eq (π : Y ⟶ X) (V : X.Opens) {O : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (r : Γ(X, V)) :
    GlobalTheory.HeatV.cst π V h r = pbT π r O := (pbT_of_le π h r).symm

theorem rsT_unit {O₀ O : Y.Opens} (h : O ≤ O₀) (w : Γ(Y, O₀)ˣ) : rsT w.val O * rsT w⁻¹.val O = 1 := by
  rw [← rsT_mul, Units.mul_inv, rsT_one h]

theorem rsT_cocycle (L : LB Y) (hL : L.IsLB) (i j k : L.ι) {O : Y.Opens} (hO : O ≤ L.U i ⊓ L.U j ⊓ L.U k) :
    rsT (L.g i j).val O * rsT (L.g j k).val O = rsT (L.g i k).val O := by
  have e := congrArg (fun u : Γ(Y, L.U i ⊓ L.U j ⊓ L.U k)ˣ => rsT u.val O) (hL.cocycle i j k)
  simp only [Units.val_mul, rsT_mul] at e
  have r : ∀ {V V' : Y.Opens} (h : V' ≤ V) (u : Γ(Y, V)ˣ), O ≤ V' →
      rsT (ReciprocityTheory.ChartRestriction.G.Semi.res h u).val O = rsT u.val O := fun h u hO' => by
    show rsT (resG Y h u.val) O = _
    rw [← rsT_of_le h, rsT_rsT h hO']
  rw [r _ _ hO, r _ _ hO, r _ _ hO] at e
  exact e

theorem exists_heatV : ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) (V : X.Opens) (L : LB Y), L.IsLB → IsUnit (2 : Γ(X, V)) → ∀ (n : ℕ) (dd : Fin n → Fld Y), (∀ a, IsField ⊤ (dd a)) → (∀ a O (h : O ≤ π ⁻¹ᵁ V) (r : Γ(X, V)), dd a O (GlobalTheory.HeatV.cst π V h r) = 0) → ∀ (Θ : Matrix (Fin n) (Fin n) Γ(X, V)), Θᵀ = Θ → ∀ (J : Type) (W : J → Y.Opens) (j : J → L.ι) (d : J → Fld Y) (hW : ∀ i, W i ≤ π ⁻¹ᵁ V), (∀ i, W i ≤ L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i i' O (h : O ≤ W i ⊓ W i') (f : Γ(Y, O)), d i O f - d i' O f = ∑ a, ∑ b, GlobalTheory.HeatV.cst π V (h.trans (inf_le_left.trans (hW i))) (Θ a b) * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) * dd a O f) → (∀ z : C1 W, IsCoc W z → ∃ (cc : Fin n → Γ(X, V)) (y : ∀ i, Γ(Y, W i)), ∀ i i', z i i' = ∑ b, GlobalTheory.HeatV.cst π V (inf_le_left.trans (hW i)) (cc b) * (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) + (rsT (y i') (W i ⊓ W i') - rsT (y i) (W i ⊓ W i'))) → ∃ (e u : Fin n → Γ(X, V)) (pf pf' : ∀ i, Γ(Y, W i)), ∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(Y, O)), GlobalTheory.HeatV.opV π V dd Θ u (fun O' f' => d i O' f' + ∑ a, pbT π (e a) O' * dd a O' f') (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 Y) (L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 Y) (L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV π V dd Θ u (fun O' f' => d i' O' f' + ∑ a, pbT π (e a) O' * dd a O' f') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f := by
  intro Y X π V L hL h2 n dd hddF _hddC Θ hΘ J W j d hW hWL hdF hKS hH1
  simp only [cst_eq] at hKS hH1
  have hdd : ∀ a (O : Y.Opens), IsDer (dd a O) := fun a O => isDer_of_isField (hddF a) le_top
  obtain ⟨t, ht⟩ : ∃ t : Γ(X, V), 2 * t = 1 := ⟨_, h2.mul_val_inv⟩
  have hc2 : ∀ O : Y.Opens, O ≤ π ⁻¹ᵁ V → 2 * pbT π t O = 1 := fun O hO => by
    have e := congrArg (fun s => pbT π s O) ht
    simp only [pbT_mul, pbT_one π hO] at e
    rw [show (2 : Γ(X, V)) = 1 + 1 from one_add_one_eq_two.symm, pbT_add, pbT_one π hO, one_add_one_eq_two] at e
    exact e
  have hs : ∀ (O : Y.Opens) a b, pbT π (Θ a b) O = pbT π (Θ b a) O := fun O a b => by
    rw [show Θ a b = Θᵀ b a from rfl, hΘ]
  have hV2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → O ≤ π ⁻¹ᵁ V := fun i i' O h => h.trans (inf_le_left.trans (hW i))
  have hm2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → O ≤ L.U (j i) ⊓ L.U (j i') := fun i i' O h =>
    le_inf (h.trans (inf_le_left.trans (hWL i))) (h.trans (inf_le_right.trans (hWL i')))
  have hm3 : ∀ i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → O ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'') :=
    fun i i' i'' O h => le_inf (le_inf (h.trans (inf_le_left.trans (inf_le_left.trans (hWL i))))
      (h.trans (inf_le_left.trans (inf_le_right.trans (hWL i'))))) (h.trans (inf_le_right.trans (hWL i'')))
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin n → J → J → ∀ O : Y.Opens, Γ(Y, O), ∀ b i i' O,
      φ b i i' O = dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O := ⟨_, fun _ _ _ _ => rfl⟩
  have rφ : ∀ b i i' (O₁ O : Y.Opens), O₁ ≤ W i ⊓ W i' → O ≤ O₁ → rsT (φ b i i' O₁) O = φ b i i' O := by
    intro b i i' O₁ O h1 h
    rw [hφ, hφ, rsT_mul, ← field_rsT (hddF b) le_top h, rsT_rsT (hm2 i i' O₁ h1) h, rsT_rsT (hm2 i i' O₁ h1) h]
  have dlc : ∀ i i' i'' (O : Y.Opens) (δ : Γ(Y, O) → Γ(Y, O)), IsDer δ → O ≤ W i ⊓ W i' ⊓ W i'' →
      δ (rsT (L.g (j i) (j i'')).val O) * rsT (L.g (j i) (j i''))⁻¹.val O =
        δ (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O +
        δ (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O := by
    intro i i' i'' O δ hδ hO
    have h3 := hm3 i i' i'' O hO
    exact hδ.dlog_mul (rsT_unit (h3.trans inf_le_left) _)
      (rsT_unit (le_inf (h3.trans (inf_le_left.trans inf_le_right)) (h3.trans inf_le_right)) _)
      (rsT_unit (le_inf (h3.trans (inf_le_left.trans inf_le_left)) (h3.trans inf_le_right)) _)
      (rsT_cocycle L hL _ _ _ h3)
  have cφ : ∀ b i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' ⊓ W i'' →
      φ b i i'' O = φ b i i' O + φ b i' i'' O := fun b i i' i'' O hO => by
    rw [hφ, hφ, hφ]; exact dlc i i' i'' O _ (hdd b O) hO
  have ks : ∀ i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' →
      d i O (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O =
        d i' O (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O +
        ∑ a, ∑ b, pbT π (Θ a b) O * φ b i i' O * φ a i' i'' O := fun i i' i'' O hO => by
    rw [← sub_eq_iff_eq_add', ← sub_mul, hKS i i' O hO, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hφ, hφ]; ring

  obtain ⟨z₁, hz₁⟩ : ∃ z : C1 W, ∀ i i', z i i' =
      -(pbT π t (W i ⊓ W i') * ∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i') *
          dd a (W i ⊓ W i') (φ b i i' (W i ⊓ W i'))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z : C1 W, ∀ i i', z i i' =
      d i (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i') -
        pbT π t (W i ⊓ W i') * ∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i') *
          φ a i i' (W i ⊓ W i') * φ b i i' (W i ⊓ W i') := ⟨_, fun _ _ => rfl⟩
  have rz₁ : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → rsT (z₁ i i') O =
      -(pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * dd a O (φ b i i' O)) := by
    intro i i' O hO
    have e : ∀ a b, rsT (dd a (W i ⊓ W i') (φ b i i' (W i ⊓ W i'))) O = dd a O (φ b i i' O) := fun a b => by
      rw [← field_rsT (hddF a) le_top hO, rφ b i i' _ O le_rfl hO]
    rw [hz₁]
    simp only [rsT_neg, rsT_mul, rsT_sum, rsT_pbT π (hV2 i i' _ le_rfl) hO, e]
  have rz₂ : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → rsT (z₂ i i') O =
      d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * φ a i i' O * φ b i i' O := by
    intro i i' O hO
    have e : ∀ b, rsT (φ b i i' (W i ⊓ W i')) O = φ b i i' O := fun b => rφ b i i' _ O le_rfl hO
    rw [hz₂]
    simp only [rsT_sub, rsT_mul, rsT_sum, rsT_pbT π (hV2 i i' _ le_rfl) hO, e]
    rw [← field_rsT (hdF i) inf_le_left hO, rsT_rsT (hm2 i i' _ le_rfl) hO, rsT_rsT (hm2 i i' _ le_rfl) hO]
  have tri : ∀ i i' i'', (W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ∧ (W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ∧
      (W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') :=
    fun _ _ _ => ⟨inf_le_left, le_inf (inf_le_left.trans inf_le_right) inf_le_right,
      le_inf (inf_le_left.trans inf_le_left) inf_le_right⟩
  have coc₁ : IsCoc W z₁ := by
    intro i i' i''
    obtain ⟨t1, t2, t3⟩ := tri i i' i''
    rw [rz₁ i i' _ t1, rz₁ i' i'' _ t2, rz₁ i i'' _ t3]
    have e := fun b => cφ b i i' i'' _ le_rfl
    simp only [e, (hdd _ _).1, mul_add, Finset.sum_add_distrib]
    ring
  have coc₂ : IsCoc W z₂ := by
    intro i i' i''
    obtain ⟨t1, t2, t3⟩ := tri i i' i''
    rw [rz₂ i i' _ t1, rz₂ i' i'' _ t2, rz₂ i i'' _ t3]
    have e := fun b => cφ b i i' i'' _ le_rfl
    simp only [e]
    rw [dlc i i' i'' _ _ (isDer_of_isField (hdF i) (t1.trans inf_le_left)) le_rfl, ks i i' i'' _ t1,
      quad_add (hs _) (fun a => φ a i i' _) (fun a => φ a i' i'' _)]
    linear_combination (∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i' ⊓ W i'') * φ b i i' _ * φ a i' i'' _) *
      hc2 _ (hV2 i i' _ t1)
  obtain ⟨c, y₁, hy₁⟩ := hH1 z₁ coc₁
  obtain ⟨e, y₂, hy₂⟩ := hH1 z₂ coc₂
  have A1 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' →
      rsT (y₁ i') O - rsT (y₁ i) O = -(pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * dd a O (φ b i i' O)) -
        ∑ b, pbT π (c b) O * φ b i i' O := by
    intro i i' O hO
    have h := congrArg (fun s => rsT s O) (hy₁ i i')
    simp only [rz₁ i i' O hO, rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_pbT π (hV2 i i' _ le_rfl) hO,
      rsT_rsT inf_le_left hO, rsT_rsT inf_le_right hO] at h
    have e' : ∀ b, rsT (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
        rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) O = φ b i i' O := fun b => by
      rw [← hφ, rφ b i i' _ O le_rfl hO]
    simp only [← rsT_mul, e'] at h
    linear_combination -h
  have A2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' →
      rsT (y₂ i') O - rsT (y₂ i) O = d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * φ a i i' O * φ b i i' O - ∑ b, pbT π (e b) O * φ b i i' O := by
    intro i i' O hO
    have h := congrArg (fun s => rsT s O) (hy₂ i i')
    simp only [rz₂ i i' O hO, rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_pbT π (hV2 i i' _ le_rfl) hO,
      rsT_rsT inf_le_left hO, rsT_rsT inf_le_right hO] at h
    have e' : ∀ b, rsT (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
        rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) O = φ b i i' O := fun b => by
      rw [← hφ, rφ b i i' _ O le_rfl hO]
    simp only [← rsT_mul, e'] at h
    linear_combination -h
  refine ⟨fun a => -e a, fun a => -c a, y₂, y₁, ?_⟩
  intro k i i' O h f
  have hO : O ≤ π ⁻¹ᵁ V := hV2 i i' O h
  rw [pbT_id (hm2 i i' O h)]
  have hg := rsT_unit (hm2 i i' O h) (L.g (j i) (j i'))
  have hdi : IsDer (fun f : Γ(Y, O) => d i O f + ∑ a, pbT π (-e a) O * dd a O f) := by
    have h1 := isDer_of_isField (hdF i) (h.trans inf_le_left)
    refine ⟨fun x y => ?_, fun x y => ?_⟩
    · simp only [h1.1, (hdd _ O).1, mul_add, Finset.sum_add_distrib]
      ring
    · have s : ∑ a, pbT π (-e a) O * (x * dd a O y + y * dd a O x) =
          x * ∑ a, pbT π (-e a) O * dd a O y + y * ∑ a, pbT π (-e a) O * dd a O x := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      simp only [h1.2, (hdd _ O).2, s]
      ring
  have key := ringOp_conj hdi (fun a => hdd a O) (Θ := Θ.map (GlobalTheory.HeatV.cst π V hO))
    (fun a b => by show GlobalTheory.HeatV.cst π V hO (Θ a b) = GlobalTheory.HeatV.cst π V hO (Θ b a)
                   rw [show Θ a b = Θᵀ b a from rfl, hΘ])
    (fun a => GlobalTheory.HeatV.cst π V hO (-c a)) (rsT (y₂ i) O) (rsT (y₁ i) O) hg k f
  refine key.trans ?_
  congr 1
  have F1 := hKS i i' O h f
  have F2 := A2 i i' O h
  have F3 := A1 i i' O h
  simp only [hφ] at F2 F3
  simp only [ringOp, GlobalTheory.HeatV.opV, Matrix.map_apply, cst_eq]
  have E : (d i O (rsT (L.g (j i) (j i')).val O) + ∑ a, pbT π (-e a) O * dd a O (rsT (L.g (j i) (j i')).val O)) *
      rsT (L.g (j i) (j i'))⁻¹.val O = d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        ∑ b, pbT π (e b) O * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) := by
    rw [add_mul, Finset.sum_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun b _ => by rw [pbT_neg]; ring
  have U1 : ∑ a, pbT π (-c a) O * (dd a O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) =
      -∑ b, pbT π (c b) O * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [pbT_neg]; ring
  rw [E, U1]
  set g := rsT (L.g (j i) (j i')).val O
  set gi := rsT (L.g (j i) (j i'))⁻¹.val O
  linear_combination (2 * (k : Γ(Y, O))) * F1 +
    (k : Γ(Y, O)) ^ 2 * f * (-2 * F2 + (∑ a, ∑ b, pbT π (Θ a b) O * (dd a O g * gi) * (dd b O g * gi)) * hc2 O hO) +
    (k : Γ(Y, O)) * f * (-2 * F3 + (∑ a, ∑ b, pbT π (Θ a b) O * dd a O (dd b O g * gi)) * hc2 O hO)

end GlobalTheory.HeatVAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFieldCoefficientsOfLinearVectorFi
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VertCoeffRing
open GlobalTheory.TangentOrigin
open GlobalTheory.KS (rsT_add rsT_mul rsT_zero)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem evalPt_lieExp {m : ℕ} (u : Fin m → TanM (𝟙 (Sp R)) G) (dd : Fin m → Fld G.left)
    (hd : ∀ i, IsInv G (u i) (dd i)) (B : Type) [CommRing B] [Algebra R B] (e : Fin m → B)
    (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens)
    (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by
  induction m with
  | zero =>
    have : GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z = z := by
      simp [GlobalTheory.SqZero.lieExp]
    rw [this]
    exact ⟨h, fun f => by simp⟩
  | succ m ih =>
    obtain ⟨h₁, H₁⟩ := ih (fun i => u i.succ) (fun i => dd i.succ) (fun i => hd i.succ) (fun i => e i.succ)
      (fun i j => he _ _)
    obtain ⟨h₂, H₂⟩ := GlobalTheory.T.value_at_invariantField_translate_sqZero (hd 0) (e 0) (he 0 0) _ O h₁
    have : GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z =
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R (e 0) (he 0 0)) ≫ tvE (u 0)) *
          (GlobalTheory.SqZero.lieExp (fun i => tvE (u i.succ)) (fun i => e i.succ) (fun i => he i.succ i.succ) * z) := by
      rw [GlobalTheory.SqZero.lieExp, GlobalTheory.SqZero.lieExp, Fin.prod_univ_succ, _root_.mul_assoc]
    rw [this]
    refine ⟨h₂, fun f => ?_⟩
    rw [H₂, H₁, H₁, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
    simp only [← _root_.mul_assoc, he, zero_mul, Finset.sum_const_zero]
    ring

theorem exists_coeff : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) →
    ∀ (W : G.left.Opens) (δ : Fld G.left), IsField W δ → (∀ O, O ≤ W → ∀ r, δ O (constFn G.hom O r) = 0) →
    ∃ c : Fin n → Γ(G.left, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  intro R _ G _ _ hs n v dd hd W δ hδ hc
  have hb := _root_.GlobalTheory.VertCoeffRing.isLieBasis_tvE v
  refine _root_.GlobalTheory.VertCoeffGlue.exists_coeff W δ dd hδ (fun a => (hd a).1) fun V V' hV hV' hVW hV'V => ?_
  exact GlobalTheory.T.existsUnique_lieBasis_coeffs_of_derivation_affineOpen _ hb dd (fun B _ _ e he z O h => evalPt_lieExp v dd hd B e he z O h) V V' hV hV' hV'V
    (fun f => rsT (δ V f) V') (fun f f' => by simp only [hδ.1 V hVW, rsT_add])
    (fun f f' => by simp only [hδ.2.1 V hVW, rsT_add, rsT_mul])
    (fun r => by simp only [hc V hVW r, rsT_zero])

end GlobalTheory.VertCoeffRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodComparisonHolds
section
theorem GlobalTheory.PeriodFamily.periodComparison_holds : GlobalTheory.Published.PeriodComparison :=
  GlobalTheory.PeriodFamily.periodComparison_of_gaussManinPeriods GlobalTheory.PeriodFamily.gaussManinPeriods_holds
end

