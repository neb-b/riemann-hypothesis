module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRedDual
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.EtFromConn

variable {p : ℕ} [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn))

theorem dual_conn {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G : PDivGroup p k}
    (hG : G.IsEt) : G.dual.IsConn :=
  PDivGroup.dual_isConn_of_isEt p k G hG

abbrev Mod {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k)
    (hG : G.IsEt) : Type :=
  Module.Dual (WittVector p k) (B.M G.dual (dual_conn hG))

def IsTr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] (σ : k →+* k') {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) (l' : Mod B G' hG') : Prop :=
  letI : Algebra k k' := σ.toAlgebra
  ∃ (hb : (G.dual.baseChange k').IsConn)
    (lb : Module.Dual (WittVector p k') (B.M (G.dual.baseChange k') hb)),
    (∀ x, lb (B.smap hb (dual_conn hG) (G.dual.toBase k') x) = WittVector.map σ (l x)) ∧
    ∀ y, l' y = lb (B.map hb (dual_conn hG')
      ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) y)


open Classical in
def tr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) : Mod B G' hG' :=
  if h : ∃ l', IsTr B σ hG' hG s l l' then Classical.choose h else 0

theorem tr_spec {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) (h : ∃ l', IsTr B σ hG' hG s l l') :
    IsTr B σ hG' hG s l (tr B hG' hG s l) := by
  rw [tr, dite_eq_left h]
  exact Classical.choose_spec h

section Red

variable {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (hG : G.IsEt)

theorem exists_redDual : ∃ r' : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)]
      Module.Dual k G.dual.RigExt,
    (∀ l m, r' l (B.red G.dual (dual_conn hG) m) = WittVector.constantCoeff (l m)) ∧
      Function.Surjective r' ∧ ∀ l, r' l = 0 ↔ ∃ l', l = p • l' := by
  haveI := B.free G.dual (dual_conn hG)
  haveI := B.finite G.dual (dual_conn hG)
  exact wittDual_reduction p k _ _ (B.red G.dual (dual_conn hG))
    (B.red_surjective G.dual (dual_conn hG)) (B.red_eq_zero G.dual (dual_conn hG))

def redDual : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)]
    Module.Dual k G.dual.RigExt :=
  Classical.choose (exists_redDual B G hG)

theorem redDual_spec :
    (∀ l m, redDual B G hG l (B.red G.dual (dual_conn hG) m) = WittVector.constantCoeff (l m)) ∧
      Function.Surjective (redDual B G hG) ∧ ∀ l, redDual B G hG l = 0 ↔ ∃ l', l = p • l' :=
  Classical.choose_spec (exists_redDual B G hG)

def rigLie : G.RigExt ≃ₗ[k] G.dual.Lie :=
  LinearEquiv.ofBijective (G.rigToLie (p_eq_zero p k))
    (PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k (p_eq_zero p k) G hG).1

def red : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt :=
  (rigLie G hG).symm.toLinearMap.comp (G.dual.rigOfOmega.dualMap.comp (redDual B G hG))

theorem rigToLie_red (l : Mod B G hG) :
    G.rigToLie (p_eq_zero p k) (red B G hG l) = G.dual.rigOfOmega.dualMap (redDual B G hG l) :=
  (rigLie G hG).apply_symm_apply _

end Red

end GlobalTheory.Dieu.EtFromConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedExtensionOfSeriesPair
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

noncomputable section

namespace GlobalTheory.Katz

theorem exists_rigMap (p : ℕ) (k : Type) [Field k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d) :
    ∃ ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))),
      (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) →
        (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) := by
  classical
  let L : MvPowerSeries (Fin d ⊕ Fin d) k →ₗ[k] (∀ n, G.A n ⊗[k] G.A n) :=
    LinearMap.pi fun n => (c.ev₂ n).toLinearMap
  let S : Submodule k (MvPowerSeries (Fin d ⊕ Fin d) k) := G.cocycles.comap L
  let T₀ : S →ₗ[k] G.cocycles := L.restrict (fun x hx => hx)
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀
  have hU := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1
  let U : (Fin d → k) →ₗ[k] G.omega :=
    { toFun := fun w => ⟨fun n => ∑ i, w i • dUnit (R := k) (c.x n i), hU w⟩
      map_add' := fun a b => Subtype.ext (funext fun n => by
        simp [add_smul, Finset.sum_add_distrib])
      map_smul' := fun r a => Subtype.ext (funext fun n => by
        simp [Finset.smul_sum, smul_smul]) }
  refine ⟨G.rigMk ∘ₗ T.prodMap U, fun s w z u hz hu => ?_⟩
  have hs : s ∈ S := by
    change L s ∈ G.cocycles
    have : L s = z.1 := funext fun n => (hz n).symm
    rw [this]; exact z.2
  have h1 : T s = z := by
    have := LinearMap.congr_fun hT ⟨s, hs⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    exact Subtype.ext (funext fun n => (hz n).symm)
  have h2 : U w = u := Subtype.ext (funext fun n => (hu n).symm)
  change G.rigMk (T s, U w) = G.rigMk (z, u)
  exact congrArg G.rigMk (Prod.ext h1 h2)

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLoweringFibreDimension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem noetherianSpace_of_isArithVar {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : NoetherianSpace X := by
  obtain ⟨N, j, hj, hjp⟩ := h.isProjOver
  haveI := h.isDomain
  haveI := h.finite
  haveI : IsNoetherian ℤ k := isNoetherian_of_isNoetherianRing_of_finite ℤ k
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  haveI : IsProper p := hjp ▸ inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  infer_instance

theorem exists_sec_fibre_dim_lt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z →
    (∀ ℓ : ℕ, topologicalKrullDim ↥(Z ∩ fib X ℓ) ≤ d) →
    ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, ∀ ℓ : ℕ, topologicalKrullDim ↥((Z \ NV P e 0 f) ∩ fib X ℓ) < d := by
  intro k _ X _ p D hX P hA d Z hZ hdim
  haveI : NoetherianSpace X := noetherianSpace_of_isArithVar hX
  have memfib : ∀ {x : X} {ℓ : ℕ}, x ∈ fib X ℓ ↔ ringChar (X.residueField x) = ℓ := Iff.rfl
  obtain ⟨hcov, hfibc, -, -, hWfib⟩ := _root_.GlobalTheory.IntFib.fib_structure k X p D hX
  have hNV : ∀ (a b : ℤ) (g : X.functionField), g ∈ P.H a b → IsOpen (NV P a b g) :=
    fun a b g hg => (_root_.GlobalTheory.HSAmp.nv_rules k X p P a b g hg).1

  obtain ⟨e₀, g, hg, hfin0⟩ := _root_.GlobalTheory.HSAmp.GenCut.exists_sections_finite k X p D hX P hA d Z hZ (hdim 0)
  have hW₀c : IsClosed (Z \ ⋃ j, NV P (e₀ j) 0 (g j)) :=
    hZ.sdiff (isOpen_iUnion fun j => hNV _ _ _ (hg j).2)

  have hpick0 : ∀ Y : irreducibleComponents ↥(Z ∩ fib X 0), ∃ y : ↥(Z ∩ fib X 0), y ∈ Y.1 ∧
      IsClosed ({y} : Set ↥(Z ∩ fib X 0)) := fun Y =>
    (isClosed_of_mem_irreducibleComponents Y.1 Y.2).exists_closed_singleton Y.2.1.nonempty
  choose q₀ hq₀ hq₀c using hpick0
  haveI : Finite (irreducibleComponents ↥(Z ∩ fib X 0)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  set W : Set X := (Z \ ⋃ j, NV P (e₀ j) 0 (g j)) ∪ ⋃ Y, closure {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} with hWdef
  have hWc : IsClosed W := hW₀c.union (isClosed_iUnion_of_finite fun _ => isClosed_closure)
  have hcl0 : ∀ Y, closure {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} ∩ fib X 0 ⊆ {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} := by
    rintro Y x ⟨hx, hx0⟩
    obtain ⟨K, hK, hKe⟩ := isClosed_induced_iff.1 (hq₀c Y)
    have hqK : ((q₀ Y : ↥(Z ∩ fib X 0)) : X) ∈ K := by
      have : q₀ Y ∈ Subtype.val ⁻¹' K := by rw [hKe]; rfl
      exact this
    have hxK : x ∈ K := closure_minimal (Set.singleton_subset_iff.2 hqK) hK hx
    have hxZ : x ∈ Z := closure_minimal (Set.singleton_subset_iff.2 (q₀ Y).2.1) hZ hx
    have : (⟨x, hxZ, hx0⟩ : ↥(Z ∩ fib X 0)) ∈ Subtype.val ⁻¹' K := hxK
    rw [hKe] at this
    exact congrArg Subtype.val this
  have hWfin : (W ∩ fib X 0).Finite := by
    refine (hfin0.union (Set.finite_range fun Y => ((q₀ Y : ↥(Z ∩ fib X 0)) : X))).subset ?_
    rintro x ⟨hx | hx, hx0⟩
    · exact Or.inl ⟨hx, hx0⟩
    · obtain ⟨Y, hY⟩ := Set.mem_iUnion.1 hx
      exact Or.inr ⟨Y, (hcl0 Y ⟨hY, hx0⟩).symm⟩

  obtain ⟨S, hSp, hWS⟩ := hWfib W hWc

  have hpick : ∀ i : (Σ ℓ : S, irreducibleComponents ↥(Z ∩ fib X (ℓ : ℕ))), ∃ y : ↥(Z ∩ fib X (i.1 : ℕ)),
      y ∈ i.2.1 ∧ IsClosed ({(y : X)} : Set X) := by
    rintro ⟨ℓ, Y⟩
    have hc : IsClosed (Z ∩ fib X ℓ) := hZ.inter (hfibc ℓ (hSp ℓ ℓ.2).ne_zero)
    obtain ⟨y, hy, hyc⟩ :=
      (isClosed_of_mem_irreducibleComponents Y.1 Y.2).exists_closed_singleton Y.2.1.nonempty
    refine ⟨y, hy, ?_⟩
    have := hc.isClosedEmbedding_subtypeVal.isClosedMap _ hyc
    rwa [Set.image_singleton] at this
  choose q hq hqc using hpick
  haveI : ∀ ℓ : S, Finite (irreducibleComponents ↥(Z ∩ fib X (ℓ : ℕ))) := fun _ =>
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hFc : IsClosed (Set.range fun i => ((q i : ↥(Z ∩ fib X (i.1 : ℕ))) : X)) := by
    rw [← Set.iUnion_singleton_eq_range]
    exact isClosed_iUnion_of_finite hqc
  set T : Set X := closure (W ∩ fib X 0) ∪ Set.range fun i => ((q i : ↥(Z ∩ fib X (i.1 : ℕ))) : X) with hTdef
  have hTc : IsClosed T := isClosed_closure.union hFc
  have hTfin : ∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite := fun ℓ =>
    ((_root_.GlobalTheory.GenFibClosure.finite_closure_inter_fib k X p D hX W hWc hWfin ℓ).union (Set.finite_range _)).subset fun x ⟨hx, hxl⟩ =>
      hx.elim (fun h => Or.inl ⟨h, hxl⟩) Or.inr

  obtain ⟨e, he, f, hf, hTNV⟩ := _root_.GlobalTheory.HSAmp.exists_pow_section_nonvanishing_on_closed k X p D hX P hA T hTc hTfin
  refine ⟨e, he, f, hf, fun ℓ => ?_⟩
  have hfo : IsOpen (NV P e 0 f) := hNV _ _ _ hf

  have key : ∀ Y ∈ irreducibleComponents ↥(Z ∩ fib X ℓ), (d : WithBot ℕ∞) ≤ topologicalKrullDim Y →
      ∃ s ∈ Y, (s : X) ∈ T := by
    intro Y hY hYd
    rcases eq_or_ne ℓ 0 with rfl | hℓ0
    · refine ⟨q₀ ⟨Y, hY⟩, hq₀ ⟨Y, hY⟩, Or.inl (subset_closure ⟨?_, (q₀ ⟨Y, hY⟩).2.2⟩)⟩
      exact Or.inr (Set.mem_iUnion.2 ⟨⟨Y, hY⟩, subset_closure rfl⟩)
    by_cases hℓS : ℓ ∈ S
    · exact ⟨q ⟨⟨ℓ, hℓS⟩, ⟨Y, hY⟩⟩, hq ⟨⟨ℓ, hℓS⟩, ⟨Y, hY⟩⟩, Or.inr ⟨_, rfl⟩⟩
    obtain ⟨s₀, -⟩ := hY.1.nonempty
    have hℓp : ℓ.Prime := by
      rcases hcov (s₀ : X) with h | ⟨ℓ', hℓ', h⟩
      · exact absurd ((memfib.1 s₀.2.2).symm.trans (memfib.1 h)) hℓ0
      · rwa [(memfib.1 s₀.2.2).symm.trans (memfib.1 h)]
    have hc : IsClosed (Z ∩ fib X ℓ) := hZ.inter (hfibc ℓ hℓ0)
    have hCi : IsIrreducible (Subtype.val '' Y) := hY.1.image _ continuous_subtype_val.continuousOn
    have hCc : IsClosed (Subtype.val '' Y) :=
      hc.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_of_mem_irreducibleComponents Y hY)
    have hCf : Subtype.val '' Y ⊆ fib X ℓ := by
      rintro _ ⟨s, -, rfl⟩
      exact s.2.2
    have hCd : (d : WithBot ℕ∞) ≤ topologicalKrullDim ↥(Subtype.val '' Y) := by
      rwa [← (Topology.IsEmbedding.subtypeVal.homeomorphImage Y).isHomeomorph.topologicalKrullDim_eq]
    obtain ⟨x, ⟨s, hsY, rfl⟩, hxg⟩ :=
      _root_.GlobalTheory.HSAmp.common_zero_of_le_dim k X p D hX P hA ℓ d (Subtype.val '' Y) e₀ g hℓp hCi hCc hCf hCd hg
    refine ⟨s, hsY, ?_⟩
    have hxW : (s : X) ∈ W := Or.inl ⟨s.2.1, hxg⟩
    rcases hWS hxW with h | h
    · exact Or.inl h
    · obtain ⟨ℓ', hℓ'S, h'⟩ := Set.mem_iUnion₂.1 h
      have : ℓ' = ℓ := (memfib.1 h').symm.trans (memfib.1 s.2.2)
      exact absurd (this ▸ hℓ'S) hℓS
  have hCsc : IsClosed {s : ↥(Z ∩ fib X ℓ) | (s : X) ∉ NV P e 0 f} :=
    (hfo.preimage continuous_subtype_val).isClosed_compl
  have hdrop := (_root_.GlobalTheory.DimDrop.dim_drop ↥(Z ∩ fib X ℓ)).1 _ d hCsc (hdim ℓ) fun Y hY hYd hsub => by
    obtain ⟨s, hsY, hsT⟩ := key Y hY hYd
    exact hsub hsY (hTNV hsT)
  have hset : Subtype.val '' {s : ↥(Z ∩ fib X ℓ) | (s : X) ∉ NV P e 0 f} = (Z \ NV P e 0 f) ∩ fib X ℓ := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s.2.1, hs⟩, s.2.2⟩
    · rintro ⟨⟨hxZ, hxN⟩, hxl⟩
      exact ⟨⟨x, hxZ, hxl⟩, hxN, rfl⟩
  rw [← hset, ← (Topology.IsEmbedding.subtypeVal.homeomorphImage _).isHomeomorph.topologicalKrullDim_eq]
  exact hdrop

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeQuotientByPGroupSections
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.Hecke.TateQuot

theorem exists_pow_inv (c n : ℕ) (h : c.Coprime n) :
    ∃ u : ℕ, ∀ {G : Type} [Monoid G] (q : G), q ^ n = 1 → q ^ (c * u) = q := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at h
    exact ⟨1, fun q _ => by rw [h, _root_.one_mul, pow_one]⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  refine ⟨(((ZMod.unitOfCoprime c h)⁻¹ : (ZMod n)ˣ) : ZMod n).val, fun q hq => ?_⟩
  have e : (c * (((ZMod.unitOfCoprime c h)⁻¹ : (ZMod n)ˣ) : ZMod n).val) % n = 1 % n := by
    rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, ← ZMod.val_one_eq_one_mod]
    congr 1
    have := (ZMod.unitOfCoprime c h).mul_inv
    rwa [ZMod.coe_unitOfCoprime] at this
  rw [pow_eq_pow_mod _ hq, e, ← pow_eq_pow_mod _ hq, pow_one]

theorem comp_pow_pt {S : Scheme.{0}} {A : Over S} [GrpObj A] {T U : Over S} (f : T ⟶ U) (g : U ⟶ A) (m : ℕ) :
    f ≫ g ^ m = (f ≫ g) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem exists_tateIsoO_quot : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ h ∈ H, h ^ c = 1) → ∀ (act' : OActN D.O A'), (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c) (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y := by
  intro p _ D R _ b N S s o c hc H A' _ _ ψ hA' hψ hGal hHc act' hact P' hP' r₁ r₂ hiso κ _ _ x β hx
  obtain ⟨I, hI⟩ := o.geom κ x β hx
  obtain ⟨e₀, rfl⟩ := hc
  have hcop : ∀ n : ℕ, n.Coprime p → (p ^ e₀).Coprime n := fun n hnp => Nat.Coprime.pow_left e₀ hnp.symm
  let Ψ : (Over.mk x ⟶ o.A) →* (Over.mk x ⟶ A') :=
    MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)
  have hΨ : ∀ t, Ψ t = t ≫ ψ := fun _ => rfl
  have hkill : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 → t ^ (p ^ e₀) = 1 := by
    intro t ht
    have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
      rw [← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]
    obtain ⟨h, hh, -⟩ := hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
    have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1 := Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)
    rw [e2, TateTransl.one_comp_transl_pt, ← comp_pow_pt, hHc h.1 h.2, MonObj.comp_one]
  have hnκ : ∀ n : ℕ, n.Coprime p → (n : κ) ≠ 0 := fun n hnp => by
    have h := (b.unit n hnp).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have ker' : ∀ n, 0 < n → n.Coprime p → ∀ y, I.ev n y ≫ ψ = 1 ↔ ∃ z, y = n • z := by
    intro n hn hnp y
    constructor
    · intro h1
      have h2 := hkill _ h1
      have h3 : I.ev n y ^ n = 1 := by
        rw [← TateTransl.ev_nsmul]; exact (I.ker n hn hnp _).2 ⟨y, rfl⟩
      have h4 : I.ev n y ^ (p ^ e₀).gcd n = 1 := pow_gcd_eq_one.2 ⟨h2, h3⟩
      rw [hcop n hnp, pow_one] at h4
      exact (I.ker n hn hnp y).1 h4
    · rintro ⟨z, rfl⟩
      rw [(I.ker n hn hnp _).2 ⟨z, rfl⟩, MonObj.one_comp]
  have htor : ∀ n, 0 < n → n.Coprime p → ∀ y, (I.ev n y ≫ ψ) ^ n = 1 := by
    intro n hn hnp y
    rw [← hΨ, ← map_pow, hΨ, ← TateTransl.ev_nsmul]
    exact (ker' n hn hnp (n • y)).2 ⟨y, rfl⟩
  have onto' : ∀ n, 0 < n → n.Coprime p → ∀ q : Over.mk x ⟶ A', q ^ n = 1 ↔ ∃ y, I.ev n y ≫ ψ = q := by
    intro n hn hnp q
    constructor
    · intro hq
      haveI := hGal.fin
      haveI := hGal.onto
      obtain ⟨a₀, ha₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left q.left
      let a : Over.mk x ⟶ o.A := Over.homMk a₀ (by
        show a₀ ≫ o.A.hom = x
        rw [← Over.w ψ, ← Category.assoc, ← ha₀, Over.w q]; rfl)
      have ha : a ≫ ψ = q := Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha₀.symm)
      have han : (a ^ n) ≫ ψ = 1 := by rw [← hΨ, map_pow, hΨ, ha, hq]
      have hanc := hkill _ han
      obtain ⟨u, hu⟩ := exists_pow_inv (p ^ e₀) n (hcop n hnp)
      have ha' : (a ^ (p ^ e₀ * u)) ^ n = 1 := by
        rw [← pow_mul, show p ^ e₀ * u * n = n * p ^ e₀ * u by ring, pow_mul, pow_mul, hanc, one_pow]
      obtain ⟨y, hy⟩ := (I.onto n hn hnp _).1 ha'
      refine ⟨y, ?_⟩
      rw [hy, ← hΨ, map_pow, hΨ, ha, hu q hq]
    · rintro ⟨y, rfl⟩
      exact htor n hn hnp y
  have hiso2 : LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e₀))
      ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb (pull_isLB o.isLB _) _ _) (pull_isLB (pull_isLB hP' _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow (pull_isLB o.isLB _), GlobalTheory.CechPic.cls_pull o.isLB, GlobalTheory.CechPic.cls_pull (pull_isLB hP' _),
      GlobalTheory.CechPic.cls_pull hP', ← GlobalTheory.CechPic.pull_comp]
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB hP' _)).2 hiso
    rw [GlobalTheory.CechPic.cls_linComb o.isLB, GlobalTheory.CechPic.cls_pull hP'] at h1
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift (𝟙 o.A) (𝟙 o.A)).left) h1
    rw [map_nsmul, ← GlobalTheory.CechPic.pull_comp] at h2
    rw [h2]
    congr 1
    simp only [sq2, ← Over.comp_left, comp_lift, Category.id_comp, lift_fst_assoc, lift_snd_assoc, Category.comp_id]
  refine ⟨⟨fun n => I.ζ n ^ (p ^ e₀), fun n hn hnp => (I.ζ_prim n hn hnp).pow_of_coprime _ (hcop n hnp), ?_,
    fun n y => I.ev n y ≫ ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun y => ?_⟩
  · intro n m hn hm hnm
    rw [← pow_mul, _root_.mul_comm (p ^ e₀) m, pow_mul, I.ζ_pow n m hn hm hnm]
  · intro n y y'
    rw [I.add, MonObj.mul_comp]
  · intro n b' y
    rw [I.lin, Category.assoc, hact, ← Category.assoc]
  · exact fun n hn hnp y => ker' n hn hnp y
  · exact fun n hn hnp q => onto' n hn hnp q
  · intro n m hn hm hnm y
    rw [← hΨ, ← map_pow, hΨ, I.tower n m hn hm hnm]
  · intro n hn hnp u v
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_weilCommutatorPairing_torsion_geometricPoint S A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) hA' (pull_isLB hP' _) κ x n hn
      (hnκ n hnp) _ _ (htor n hn hnp u) (htor n hn hnp v)
    have h3 := (GlobalTheory.weilIs_along_hom GlobalTheory.globalFns_holds S o.A A' ψ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left)
      (P'.pull (lift (𝟙 A') (𝟙 A')).left) (p ^ e₀) n (Over.mk x) (I.ev n u) (I.ev n v)
      (unitOn (I.ζ n ^ (2 * D.EF u v))) e o.ab hA' (pull_isLB o.isLB _) (pull_isLB hP' _) hψ hiso2 he).2
      (I.isom n hn hnp u v)
    rw [h3] at he
    convert he using 2
    show unitOn ((I.ζ n ^ (p ^ e₀)) ^ (2 * D.EF u v)) = unitOn (I.ζ n ^ (2 * D.EF u v)) ^ (p ^ e₀)
    rw [unitOn, unitOn, ← map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  · show toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y ≫ ψ
    rw [← Category.assoc, hI]

end GlobalTheory.UPel.HT.Hecke.TateQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeightedPairOrbitsOfFiniteWeightedFixedPoiStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_weightedPairOrbits_of_finite_weightedFixedPoints : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), Set.Finite {q : Pts G v β x t hx Kf K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} → {o : MulAction.orbitRel.Quotient (grp G β) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') | ∃ y, GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y ≠ 0}.Finite := by
  first | (exact @GlobalTheory.CxUnfold.finite_orbits_of_finite_pts) | (exact GlobalTheory.CxUnfold.finite_orbits_of_finite_pts) | (intros; apply GlobalTheory.CxUnfold.finite_orbits_of_finite_pts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHopfAlgebraEqRangeMulKernel
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_eq_range_mul_ker : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A]
    [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
    [Module.Finite k C] (f : C →ₐc[k] A),
    Module.finrank k A = Module.finrank k (LinearMap.range (f : C →ₐ[k] A).toLinearMap) *
      Module.finrank k (A ⧸ kerIdeal f) := by
  intro k _ A _ _ _ _ C _ _ _ _ f
  rw [GlobalTheory.PDiv.finrank_eq_ker_mul_range k A C f, mul_comm]

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSupportBoundedByUniformizerPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_support_bounded_by_uniformizer_pow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → (∀ j, j < G.m → ∀ r s, (j + 1 = G.m → r ≠ topLast G (j + 1)) → valuation k (x j r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ i, i < G.m → ∀ r s, valuation k (y i r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  first | exact @GlobalTheory.FunObj.FlatSupp.flatTensor_support | exact GlobalTheory.FunObj.FlatSupp.flatTensor_support | (intros; apply GlobalTheory.FunObj.FlatSupp.flatTensor_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserFixesVacuumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_lattice_stabiliser_fixes_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  first | exact @GlobalTheory.InertSph.vac_fixed | exact GlobalTheory.InertSph.vac_fixed | (intros; apply GlobalTheory.InertSph.vac_fixed <;> assumption)
end

