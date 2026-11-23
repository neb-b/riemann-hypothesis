module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeterminantCharacterIdentity
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClassScalarCompare

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity MvPolynomial
open scoped nonZeroDivisors Classical TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Poly

variable (c : Coeff l) {n : ℕ}

end Poly

section Adelic

variable {n : ℕ}

theorem star_diagE (x : E) : star (diagE E x) = diagE E (IsCMField.complexConj E x) := by
  show adConj E (1 ⊗ₜ x) = 1 ⊗ₜ _
  simp [adConj]

theorem map_conjTranspose (g : Matrix (Fin n) (Fin n) E) :
    g.conjTranspose.map (diagE E) = star (g.map (diagE E)) := by
  ext a b; exact (star_diagE _).symm

def toRat (g : Matrix (Fin n) (Fin n) E) (hg : g.conjTranspose * g = 1) : ratPts E n :=
  ⟨⟨g.map (diagE E), Matrix.mem_unitaryGroup_iff'.2 (by
      rw [← map_conjTranspose, ← Matrix.map_mul, hg, Matrix.map_one _ (map_zero _) (map_one _)])⟩,
    fun a b => ⟨g a b, rfl⟩, fun a b => ⟨_, (star_diagE (g b a)).symm⟩⟩

def adTrace : AdE E →+ AdF E :=
  ((TensorProduct.rid (maximalRealSubfield E) (AdF E)).toLinearMap ∘ₗ
    LinearMap.lTensor (AdF E) (Algebra.trace (maximalRealSubfield E) E)).toAddMonoidHom

end Adelic

section Conj

variable {n : ℕ}

theorem conj_smul (o : 𝓞 E) (x : E) :
    IsCMField.complexConj E (o • x) = IsCMField.ringOfIntegersComplexConj E o • IsCMField.complexConj E x := by
  show IsCMField.complexConj E ((o : E) * x) = _
  rw [map_mul]; rfl

def conjMod (M : Submodule (𝓞 E) E) : Submodule (𝓞 E) E where
  carrier := {x | IsCMField.complexConj E x ∈ M}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show IsCMField.complexConj E (a + b) ∈ M
    rw [map_add (IsCMField.complexConj E)]
    exact M.add_mem ha hb
  smul_mem' := fun o x hx => by
    show IsCMField.complexConj E (o • x) ∈ M
    rw [conj_smul]; exact M.smul_mem _ hx

theorem mem_conjMod {M : Submodule (𝓞 E) E} {x : E} : x ∈ conjMod M ↔ IsCMField.complexConj E x ∈ M := Iff.rfl

theorem bar_bar (H : Host E) (o : 𝓞 E) : H.bar (H.bar o) = o := by
  ext; rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem mem_conjId (I : Ideal (𝓞 E)) (o : 𝓞 E) : o ∈ conjId H I ↔ H.bar o ∈ I := by
  rw [conjId, Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa [bar_bar] using hx
  · intro h; exact ⟨_, h, bar_bar H o⟩

theorem conjMod_idlE (H : Host E) (I : Ideal (𝓞 E)) : conjMod (idlE I) = idlE (conjId H I) := by
  ext x
  rw [mem_conjMod]
  constructor
  · rintro ⟨o, ho, h⟩
    refine ⟨H.bar o, (mem_conjId I _).2 (by rwa [bar_bar]), ?_⟩
    have h' : (o : E) = IsCMField.complexConj E x := h
    show ((H.bar o : 𝓞 E) : E) = x
    rw [H.bar_eq, h', IsCMField.complexConj_apply_apply]
  · rintro ⟨o, ho, rfl⟩
    exact ⟨H.bar o, (mem_conjId I _).1 ho, H.bar_eq o⟩

theorem smul_eq_idlE_mul (I : Ideal (𝓞 E)) (M : Submodule (𝓞 E) E) : I • M = idlE I * M := by
  refine le_antisymm (Submodule.smul_le.2 fun a ha x hx => ?_) (Submodule.mul_le.2 ?_)
  · exact Submodule.mul_mem_mul (⟨a, ha, rfl⟩ : (a : E) ∈ idlE I) hx
  · rintro _ ⟨a, ha, rfl⟩ x hx
    exact Submodule.smul_mem_smul ha hx

def conjLat (L : Submodule (𝓞 E) (Fin n → E)) : GenLat E n where
  La :=
  { carrier := {v | (fun j => IsCMField.complexConj E (v j)) ∈ L}
    zero_mem' := by
      show (fun j => IsCMField.complexConj E 0) ∈ L
      rw [map_zero]; exact L.zero_mem
    add_mem' := fun {a b} ha hb => by
      show (fun j => IsCMField.complexConj E (a j + b j)) ∈ L
      simp only [map_add (f := _)]; exact add_mem ha hb
    smul_mem' := fun o x hx => by
      show (fun j => IsCMField.complexConj E (o • x j)) ∈ L
      simp only [conj_smul]; exact L.smul_mem _ hx }

theorem mem_conjLat {L : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E} :
    v ∈ (conjLat L).La ↔ (fun j => IsCMField.complexConj E (v j)) ∈ L := Iff.rfl

theorem conjLat_conjLat (L : Submodule (𝓞 E) (Fin n → E)) : (conjLat (conjLat L).La).La = L := by
  ext v; simp [mem_conjLat]

theorem latPin_iff_conjLat {Cl : Type} (Lh : Cl → Submodule (𝓞 E) (Fin n → E)) (La : Cl → GenLat E n) :
    LatPin Lh La ↔ ∀ k, La k = conjLat (Lh k) :=
  forall_congr' fun k => ⟨fun h => congrArg GenLat.mk (Submodule.ext h), fun h v => by rw [h, mem_conjLat]⟩

theorem conjLat_std : conjLat (stdLat E n) = ⟨stdLat E n⟩ := by
  have hc (x : E) (hx : IsIntegral ℤ x) : IsIntegral ℤ (IsCMField.complexConj E x) :=
    hx.map_of_comp_eq (RingHom.id ℤ) (IsCMField.complexConj E : E →+* E) (RingHom.ext_int _ _)
  refine congrArg GenLat.mk (Submodule.ext fun v => ?_)
  show _ ∈ stdLat E n ↔ _
  simp only [GlobalTheory.StdHarm.mem_std]
  exact forall_congr' fun j => ⟨fun h => by simpa using hc _ h, hc _⟩

def stdIndex (Λ : GenLat E n) : ℕ := (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index

theorem stdIndex_conjLat (L : Submodule (𝓞 E) (Fin n → E)) : stdIndex (conjLat L) = stdIndex ⟨L⟩ := by
  let f : (Fin n → E) →+ (Fin n → E) := (IsCMField.complexConj E : E →+ E).compLeft (Fin n)
  have h1 : (conjLat L).Ln.toAddSubgroup = (L ⊓ stdLat E n).toAddSubgroup.comap f := by
    ext v
    have : v ∈ stdLat E n ↔ v ∈ (conjLat (stdLat E n)).La := by rw [conjLat_std]
    exact and_congr_right fun _ => this
  have h2 : (conjLat L).La.toAddSubgroup.map f = L.toAddSubgroup := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hv
      refine ⟨f v, ?_, funext fun j => IsCMField.complexConj_apply_apply E (v j)⟩
      rw [← conjLat_conjLat L] at hv
      exact hv
  show AddSubgroup.relIndex _ _ = AddSubgroup.relIndex _ _
  rw [h1, AddSubgroup.relIndex_comap, h2]
  rfl

end Conj

section Scalar

variable (c : Coeff l) {n : ℕ}

theorem absNorm_ne_zero {cc : Ideal (𝓞 E)} (h1 : cc ⊔ conjId H cc = ⊤) : Ideal.absNorm cc ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  rintro rfl
  simp [conjId] at h1

def Guard (H : Host E) (bad : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  (⟨L⟩ : GenLat E n).Unimod ∧ (⟨L⟩ : GenLat E n).TrivAt bad ∧ GenLat.SplitSupp H (⟨L⟩ : GenLat E n)

end Scalar

section Comparison₂

variable (c : Coeff l) {n : ℕ} {T : Type} [AddCommGroup T] [Module c.F T] [Module (𝓞 c.F) T]
  [IsScalarTower (𝓞 c.F) c.F T]

end Comparison₂

section Twist

variable (c : Coeff l) {n : ℕ} {T : Type} [AddCommGroup T] [Module c.F T] [Module (𝓞 c.F) T]
  [IsScalarTower (𝓞 c.F) c.F T]

end Twist

section Indep

variable (Xo : Moduli Dw l) (c : Coeff l) {n : ℕ}

theorem smul_conjLat_le {m m' : 𝓞 E} (e : (m' : E) = IsCMField.complexConj E (m : E))
    {M M' : Submodule (𝓞 E) (Fin n → E)} (hM : Ideal.span {m} • M ≤ M') :
    Ideal.span {m'} • (conjLat M).La ≤ (conjLat M').La := by
  rw [Submodule.ideal_span_singleton_smul] at hM ⊢
  rintro _ ⟨v, hv, rfl⟩
  have := hM ⟨_, hv, rfl⟩
  rw [mem_conjLat]
  convert this using 1
  funext j
  show IsCMField.complexConj E ((m' : E) * v j) = (m : E) * _
  rw [map_mul, e, IsCMField.complexConj_apply_apply]

theorem guard_conjLat {bad : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (g : Guard H bad L) :
    Guard H bad (conjLat L).La := by
  obtain ⟨g1, ⟨k, k0, k1, k2⟩, m, m0, m1, m2, m3⟩ := g
  have hs : (conjLat (stdLat E n)).La = stdLat E n := by rw [conjLat_std]
  have hc : ∀ x : E, IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range ↔ x ∈ (algebraMap (𝓞 E) E).range := by
    have : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range → IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range := by
      rintro _ ⟨o, rfl⟩; exact ⟨H.bar o, H.bar_eq o⟩
    exact fun x => ⟨fun h => by simpa using this _ h, this x⟩
  refine ⟨fun v => ?_, ⟨k, k0, ?_, ?_⟩, H.bar m, by simpa using m0, ?_, ?_, fun P hP hm hfix => ?_⟩
  · refine (g1 fun j => IsCMField.complexConj E (v j)).trans ⟨fun h w hw => ?_, fun h w hw => ?_⟩
    · rw [← hc]
      simpa using h _ hw
    · rw [← hc]
      simpa using h (fun j => IsCMField.complexConj E (w j)) (by simpa [mem_conjLat] using hw)
  · exact hs ▸ smul_conjLat_le (by simp) k1
  · exact hs ▸ smul_conjLat_le (by simp) k2
  · exact hs ▸ smul_conjLat_le (H.bar_eq m) m1
  · exact hs ▸ smul_conjLat_le (H.bar_eq m) m2
  · exact m3 P hP (hfix ▸ (mem_conjId P m).2 hm) hfix

variable {Cl : Type} [Fintype Cl] {T : Type} [AddCommGroup T] [Module c.F T]

end Indep

end GlobalTheory.ClassScalarCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RdUMulApply
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory

theorem rdU_mul_apply : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (f f' : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r), rdU U (f * f') k x = rdU U f k x * rdU U f' k x := by
  intro E _ _ _ H Dw l Xo c σ r U f f' k x
  classical
  by_cases h : x ∈ (U.X k).dom
  · have e := evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f f' (U.un k ⟨x, h⟩)
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]
    exact e
  · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h, mul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsFrameRatio
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem sec_eq_scal_of_values (hT : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {V : Type}
    (x : Sp ℂ ⟶ Xo.X) (ex : V → (Over.mk x ⟶ Xo.univ.t.G)) (hex : Function.Surjective ex)
    (s s' : LB.Sec (PPx x)) (hs : SecGen x s) (t : ℂ)
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ Formalism.L2.PjFree.gxFst x = (ex z).left → pt ≫ Formalism.L2.PjFree.gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s'.f (fun _ => j)) =
        t * valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j))) :
    ∀ i, s'.f i = scal x t i * s.f i := by
  obtain ⟨h1, h2, -⟩ := sec_values_complex_fibre hT E H Dw l Xo x s
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨i, pt, hp, hne⟩ := h2.1 hs
  have hi : i = fun _ => i (0 : Fin 1) := funext fun k => congrArg i (Subsingleton.elim _ _)
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨_, hi⟩
  have cond : Formalism.L2.PjFree.gxFst x ≫ Xo.univ.t.G.hom = Formalism.L2.PjFree.gxSnd x ≫ x := pullback.condition.symm
  obtain ⟨z, hz⟩ := hex (Over.homMk (pt ≫ Formalism.L2.PjFree.gxFst x) (by
    show (pt ≫ Formalism.L2.PjFree.gxFst x) ≫ Xo.univ.t.G.hom = x
    rw [Category.assoc, cond, ← Category.assoc, hp, Category.id_comp]))
  have hz' : pt ≫ Formalism.L2.PjFree.gxFst x = (ex z).left := by rw [hz]; rfl
  have hU : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U (fun _ => j) := by
    by_contra h
    exact hne (by unfold valAt'; rw [dite_eq_right h])
  have hU' : ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    rw [← hz']
    intro p hp'
    exact Set.mem_iInter.1 (hU hp') (0 : Fin 1)
  have e := hv j z pt hz' hp hU'
  have e' := (congrArg (valAt' pt ((PPx x).U (fun _ => j))) (ha (fun _ => j))).trans (h1 a _ pt hp)
  have hat : a = t := mul_right_cancel₀ hne (e'.symm.trans e)
  rw [← hat]
  exact ha

theorem isCombAt_single_of_isTanAt {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S]
    (x : Sp S ⟶ Xo.X) {m : ℕ} (u : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (tan : ∀ j, IsTanAt x (u j))
    (i : Fin m) : IsCombAt x u (Pi.single i 1) (u i) := by
  obtain ⟨N, _, _, v, ρ, -, h2, h3, -⟩ := TanMod.exists_tangent_module E H Dw l Xo S x
  choose n hn using fun j => (h2 _).1 (tan j)
  obtain rfl : u = fun j => v (n j) := funext fun j => (hn j).symm
  rw [h3]
  show v (n i) = _
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp)]
  simp

theorem appLE_id_apply_self {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom f = f := by
  have : Scheme.Hom.appLE (𝟙 X) U U h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (X.presheaf.map_id _)
  rw [this]
  rfl

theorem frBor_of_isThetaPt : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ : ℂ) (t₀ : (CAt σ)ˣ) (y y' : FrPt Xo c (CAt σ)), IsThetaPt T b κ y → IsThetaPt T b (Formalism.L2.PjFree.toC (t₀ : CAt σ) * κ) y' → FrBor (fun i => Option.elim i t₀ (fun _ => 1)) y y' := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb κ t₀ y y' hy hy'
  have hP := T.isPer _ hb
  obtain ⟨x, xo, u, tan, eig, basis, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', basis', s', gen'⟩ := y'
  obtain ⟨hx, hu, hs⟩ := hy
  obtain ⟨hx', hu', hs'⟩ := hy'
  dsimp only at hx hu hs hx' hu' hs'
  subst hx hx'
  obtain ⟨-, hd, -⟩ := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ hP
  have huu : ∀ τ i, u' τ i = u τ i := fun τ i => (hd _).unique (hu' τ i) (hu τ i)
  refine ⟨rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩, 𝟙 _,
    Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
  · show IsCombAt _ (u τ) _ (u' τ i)
    rw [huu]
    exact isCombAt_single_of_isTanAt (S := CAt σ) _ _ (tan τ) i
  · have key := sec_eq_scal_of_values hT (F.u k (T.Pf (T.co b))) (F.ex k (T.Pf (T.co b))) (F.ex_onto k _ hP)
      s s' gen (Formalism.L2.PjFree.toC (t₀ : CAt σ)) (fun j z pt h1 h2 h3 => by
        refine (hs' j z pt h1 h2 h3).trans ?_
        refine Eq.trans ?_ (congrArg (Formalism.L2.PjFree.toC (t₀ : CAt σ) * ·) (hs j z pt h1 h2 h3).symm)
        ring)
    refine Eq.trans ?_ (key i).symm
    exact appLE_id_apply_self _ h _

end GlobalTheory
end

