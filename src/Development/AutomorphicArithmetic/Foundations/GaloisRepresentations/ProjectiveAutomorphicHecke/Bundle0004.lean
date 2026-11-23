module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import GroundTheory.GlobalFields.Adele.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PFinToHecke
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pFinToHecke_of :
    UpperTheory.Gal.CertificateRingHomMap.FinToHecke := by
  intro E _ _ ψ m ho hk
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E m
  let p : Neutral.B1.Ideles E →* (Af E)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E) : _ →* _)
  have hpc : Continuous p := Continuous.units_map _ continuous_snd
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ ho
  have hd : ∀ k : Eˣ, p (Neutral.B1.diagUnits E k) = diagF E k := fun k => Units.ext rfl
  have hl : ∀ (w : Plc E) y, p (Neutral.B1.localIdele E w y) = sgl w y := fun w y => Units.ext rfl
  have hi : ∀ k : Eˣ, p (infDiag k) = 1 := fun k => by
    rw [infDiag_eq]
    exact Units.ext rfl
  let θ : Neutral.B1.Ideles E →* ℂˣ := ψ.comp p * f
  have hθ : ∀ x, ((θ x : ℂˣ) : ℂ) = ((ψ (p x) : ℂˣ) : ℂ) * infPow m x := fun x => by
    rw [← hfe]
    rfl
  refine ⟨⟨θ, (hψ.comp hpc).mul hf, fun k => Units.ext ?_⟩, fun k _ => ?_, fun w y => ?_⟩
  · rw [hθ, hd, hk, infPow_diagUnits, Units.val_one]
    exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ (by simp))
  · show ((θ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hθ, hi, infPow_infDiag, infPow_diagUnits, map_one, Units.val_one, one_mul]
  · show θ (Neutral.B1.localIdele E w y) = _
    refine Units.ext ?_
    rw [hθ, hl, infPow_localIdele, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PFormGU
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.LKDef.HeckeTraceForms (forms)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem rop_single {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (u : H) (Φ : H → V) (g : H) :
    rop (Finsupp.single u 1) Φ g = Φ (g * u) := by
  unfold rop
  rw [Finsupp.sum_single_index (by simp), one_smul]

private theorem rop_sum {H V Y : Type} [Group H] [AddCommGroup V] [Module ℂ V] (R : Finset Y) (e : Y → H) (Φ : H → V) (g : H) :
    rop (∑ y ∈ R, Finsupp.single (e y) 1) Φ g = ∑ y ∈ R, Φ (g * e y) := by
  unfold rop
  rw [Finsupp.sum_finsetSum _ _ _ (by simp) (by simp [add_smul])]
  exact Finset.sum_congr rfl fun y _ => by rw [Finsupp.sum_single_index (by simp), one_smul]

private structure HI {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (U : Submodule ℂ (UA E n → ℂ)) (S : Finset (Plc E)) where
  w : Plc E
  hw : IsSplitAt w
  h1 : w ∉ S
  h2 : cj w ∉ S
  B : Multiset ℂˣ
  hB : SatU U w B
  p : w.adicCompletion E
  hp : Formalism.UG.IsUnifV E w p
  i : ℕ
  hi : i ≤ n

set_option maxHeartbeats 1600000 in
theorem pFormGU_of (hExt : ExtEig2) (hCl : ClassFin) (hXi : XiZeta) (hKer : KerFormU) (hHk : HeckePres) (hSat : SatVal)
    (hMem : LocMem) (hComm : LocComm) (hOp : LevOpen) (hU : OfUBij) : FormGU := by
  intro E _ _ _ n x ζ hζ π W j Up w₀ hw₀ S Kw hS χ hχ f hf hf0 hfix
  obtain ⟨-, hap, -, -, hcc, -⟩ := hComm E n w₀ hw₀
  have hc0 : cj w₀ ∉ S := (hS.up w₀ hS.mem hw₀).2
  let Kw' := Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype)
  have mem' : ∀ k : GUf E n, k ∈ lev S Kw' ↔ k ∈ lev S Kw ∧ ∃ h : comp w₀ k ∈ Kw w₀, χ ⟨_, h⟩ = 1 := by
    intro k
    have e0 : comp w₀ k ∈ Kw' w₀ ↔ ∃ h : comp w₀ k ∈ Kw w₀, χ ⟨_, h⟩ = 1 := by
      simp only [Kw', Function.update_self, Subgroup.mem_map, MonoidHom.mem_ker]
      exact ⟨fun ⟨y, hy, e⟩ => ⟨e ▸ y.2, by rw [← hy]; congr 1; exact Subtype.ext e.symm⟩, fun ⟨h, e⟩ => ⟨⟨_, h⟩, e, rfl⟩⟩
    have e1 : ∀ w, w ≠ w₀ → Kw' w = Kw w := fun w hw => Function.update_of_ne hw _ _
    rw [mem_lev, mem_lev]
    constructor
    · rintro ⟨a, b, c⟩
      obtain ⟨h, hh⟩ := e0.1 (b _ hS.mem)
      refine ⟨⟨a, fun w hw => ?_, c⟩, h, hh⟩
      by_cases e : w = w₀
      · subst e; exact h
      · rw [← e1 w e]; exact b w hw
    · rintro ⟨⟨a, b, c⟩, h⟩
      refine ⟨a, fun w hw => ?_, c⟩
      by_cases e : w = w₀
      · subst e; exact e0.2 h
      · rw [e1 w e]; exact b w hw
  have hopen : IsOpen (lev S Kw' : Set (GUf E n)) := by
    refine hOp E n S Kw' fun w hw => ?_
    by_cases e : w = w₀
    · subst e
      simp only [Kw', Function.update_self]
      exact (hS.opn w hw).isOpenMap_subtype_val _ hχ
    · simp only [Kw', Function.update_of_ne e]; exact hS.opn w hw
  have hfix' : ∀ u : finU (E := E) (n := n), ofU u ∈ lev S Kw' → algRep W u f = f := fun u hu => by
    obtain ⟨a, h, e⟩ := (mem' _).1 hu
    have := hfix u a h
    rwa [show χ ⟨cLoc w₀ u.1, h⟩ = 1 from e, Units.val_one, one_smul] at this
  obtain ⟨φ, hφ, hφu, hφ0⟩ := hKer E n W j f hf0 (lev S Kw') (fun k hk => (mem_lev.1 hk).1) hfix'
  have hloc : ∀ y : Kw w₀, loc hw₀ y.1 ∈ lev S Kw := fun y => (hMem E n S Kw w₀ hw₀ hc0 y.1).1 hS.mem y.2
  choose R hR1 hR2 using fun a : HI π.V S => hHk E n a.w a.hw a.p a.hp a.i
  have hsv : ∀ (w : Plc E) (hw : IsSplitAt w), w ∉ S → cj w ∉ S → ∀ B, SatU π.V w B →
      IsSatVecGL w ((algRep W).comp (locF hw)) f B := fun w hw h1 h2 B hB =>
    hSat E n π W f hf hf0 w hw (fun k hk => hfix' _ ((hMem E n S Kw' w hw h2 k).2 h1 hk)) B hB
  obtain ⟨Φ, hΦ, hΦ0, heig, ψ, hψ⟩ := hExt (Gam0 E n) (GUf E n) AfQˣ (Af E)ˣ _ rat (lev S Kw') (xi0 W j) sim ζ hζ.central
    (by
      obtain ⟨s, hs⟩ := hCl E ((lev S Kw').comap ζ) (hopen.preimage hζ.cont)
      refine ⟨s, fun z => ?_⟩
      obtain ⟨t, ht, o, ho, k, e⟩ := hs z
      obtain ⟨γ, h1, h2⟩ := hXi E n W j x ζ hζ k
      exact ⟨t, ht, o, _, e, ho, γ, _, h1, h2⟩)
    φ hφ hφ0 (Kw w₀ ⊕ HI π.V S)
    (Sum.elim (fun y => Finsupp.single (loc hw₀ y.1) 1) fun a => ∑ y ∈ R a, Finsupp.single (loc a.hw y) 1)
    (Sum.elim (fun y => (χ y : ℂ)) fun a => satEig (Formalism.UG.qV E a.w) n a.B a.i)
    (by
      rintro (y | a) u hu
      · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hu)
        rfl
      · obtain ⟨y, -, hy⟩ := Finsupp.mem_support_finsetSum u hu
        obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hy)
        rfl)
    (by
      rintro (y | a) Ψ hΨ
      · refine ⟨fun γ g => ?_, fun k hk g => ?_⟩
        · simp only [Sum.elim_inl, rop_single, mul_assoc, hΨ.1]
        · simp only [Sum.elim_inl, rop_single]
          obtain ⟨a, h, e⟩ := (mem' _).1 hk
          have hk' : (loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1 ∈ lev S Kw' := by
            have h' : comp w₀ ((loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1) = (y⁻¹ * ⟨_, h⟩ * y : Kw w₀) := by
              rw [map_mul, map_mul, map_inv, comp_loc]; rfl
            have h'' : comp w₀ ((loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1) ∈ Kw w₀ := by rw [h']; exact Subtype.property _
            refine (mem' _).2 ⟨mul_mem (mul_mem (inv_mem (hloc y)) a) (hloc y), h'', ?_⟩
            rw [show (⟨_, h''⟩ : Kw w₀) = y⁻¹ * ⟨_, h⟩ * y from Subtype.ext h', map_mul, map_mul, e, map_inv, mul_one,
              inv_mul_cancel]
          rw [← hΨ.2 _ hk' (g * loc hw₀ y.1)]
          simp only [mul_assoc, mul_inv_cancel_left]
      · have := hR2 a S Kw' a.h1 a.h2 _ (xi0 W j) Ψ hΨ
        convert this using 1
        funext g
        exact rop_sum _ _ _ _)
    (by
      rintro (y | a) g hg
      · obtain ⟨u, rfl⟩ := (hU E n).2 g hg
        simp only [Sum.elim_inl, rop_single]
        have h : cLoc w₀ (locF hw₀ y.1).1 ∈ Kw w₀ := by rw [cLoc_locF]; exact y.2
        have e := hfix (locF hw₀ y.1) (hloc y) h
        rw [show (⟨_, h⟩ : Kw w₀) = y from Subtype.ext (cLoc_locF _ _)] at e
        rw [show ofU u * loc hw₀ y.1 = ofU (u * locF hw₀ y.1) from (map_mul ofU _ _).symm, hφu, hφu]
        rw [Subgroup.coe_mul, ← algForms.val_algRep, e]
        rfl
      · obtain ⟨u, rfl⟩ := (hU E n).2 g hg
        simp only [Sum.elim_inr, rop_sum]
        have e := (hsv a.w a.hw a.h1 a.h2 a.B a.hB).2.2.2 a.p a.hp a.i a.hi
        rw [hR1 a] at e
        have e2 : ∀ y, φ (ofU u * loc a.hw y) = algForms.val (((algRep W).comp (locF a.hw)) y f) u.1 := fun y => by
          rw [show ofU u * loc a.hw y = ofU (u * locF a.hw y) from (map_mul ofU _ _).symm, hφu]
          rfl
        simp only [e2]
        let L : algForms W →ₗ[ℂ] Module.Dual ℂ W.Sp :=
          { toFun := fun F => algForms.val F u.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
        have e3 := congrArg L e
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_smul] at e3
        rw [hφu]
        exact e3)
  refine ⟨Φ, ψ, ⟨hΦ0, hΦ.1, fun k hk h g => ?_, fun w hw h1 h2 B hB => ⟨hΦ0, ?_, (hsv w hw h1 h2 B hB).2.2.1, fun p hp i hi => ?_⟩⟩, hψ.1⟩
  · have h1 := congrFun (heig (Sum.inl ⟨_, h⟩)) g
    simp only [Sum.elim_inl, rop_single, Pi.smul_apply] at h1
    have h' : comp w₀ ((loc hw₀ (comp w₀ k))⁻¹ * k) = 1 := by rw [map_mul, map_inv, comp_loc, inv_mul_cancel]
    have h'' : comp w₀ ((loc hw₀ (comp w₀ k))⁻¹ * k) ∈ Kw w₀ := by rw [h']; exact one_mem _
    have hk' : (loc hw₀ (comp w₀ k))⁻¹ * k ∈ lev S Kw' :=
      (mem' _).2 ⟨mul_mem (inv_mem (hloc ⟨_, h⟩)) hk, h'', by
        rw [show (⟨_, h''⟩ : Kw w₀) = 1 from Subtype.ext h', map_one]⟩
    rw [← h1, ← hΦ.2 _ hk' (g * loc hw₀ (comp w₀ k)), mul_assoc, mul_inv_cancel_left]
  · exact GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext fun g => hΦ.2 _ ((hMem E n S Kw' w hw h2 k).2 h1 hk) g
  · let a : HI π.V S := ⟨w, hw, h1, h2, B, hB, p, hp, i, hi⟩
    have h3 := heig (Sum.inr a)
    rw [show heckeVec _ _ _ Φ = _ from hR1 a _ _ Φ]
    refine Eq.trans ?_ h3
    funext g
    rw [Finset.sum_apply]
    exact (rop_sum _ _ _ _).symm

end UpperTheory.Gal.CertificateRingHomMap
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PHeckePres
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep
open GlobalTheory.LFun (KGL heckeVec)
open GlobalTheory.Cong (Apart)
open GlobalTheory.LKDef.HeckeTraceForms (forms)
open Formalism.UG (Tj Ov IsUnifV)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem hecke_eq_sum {G : Type} [Group G] (K : Subgroup G) (h : G → ℂ) (h01 : ∀ g, h g ≠ 0 → h g = 1)
    (hfin : {q : G ⧸ K | h q.out ≠ 0}.Finite) : ∃ R : Finset G,
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V),
        heckeVec ρ K h x = ∑ g ∈ R, ρ g x := by
  refine ⟨hfin.toFinset.image Quotient.out, ?_⟩
  intro V _ _ ρ x
  rw [Finset.sum_image (fun a _ b _ e => Quotient.out_injective e)]
  have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ hfin.toFinset := by
    intro q hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by simp [h0])
  have hsum : heckeVec ρ K h x = ∑ q ∈ hfin.toFinset, h q.out • ρ q.out x :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [h01 _ ((Set.Finite.mem_toFinset hfin).1 hq), one_smul]

private theorem tj_one {L : Type} [Field L] {n : ℕ} {O : Subring L} {ϖ : L} {j : ℕ} (g : GL (Fin n) L)
    (hg : Tj ℂ n O ϖ j g ≠ 0) : Tj ℂ n O ϖ j g = 1 := by
  unfold Tj at hg ⊢
  exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero hg) _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem sum_mem_forms (hC : LocComm) (hM : LocMem) {w : Plc E} (hw : IsSplitAt w) {h : GLw n w → ℂ}
    (hh : h ∈ Formalism.UG.Hecke ℂ (KGL w (n := n))) {R : Finset (GLw n w)}
    (hR : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw n w) V) (v : V),
      heckeVec ρ (KGL w (n := n)) h v = ∑ g ∈ R, ρ g v)
    {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} (hS : w ∉ S) (hcS : cj w ∉ S)
    {V : Type} [AddCommGroup V] [Module ℂ V] {ξ : Representation ℂ (Gam0 E n) V} {Φ : GUf E n → V}
    (hΦ : Φ ∈ forms rat (lev S Kw) ξ) :
    (fun g => ∑ y ∈ R, Φ (g * loc hw y)) ∈ forms rat (lev S Kw) ξ := by
  have hloc : ∀ y ∈ KGL w (n := n), loc hw y ∈ lev S Kw := fun y hy => (hM E n S Kw w hw hcS y).2 hS hy
  let ρ : Representation ℂ (GLw n w) (GUf E n → V) := (rightReg ℂ (GUf E n) V).comp (loc hw)
  have hρ : ∀ y (f : GUf E n → V) g, ρ y f g = f (g * loc hw y) := fun _ _ _ => rfl
  have hfix : Φ ∈ fixed ρ (KGL w (n := n)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    funext g
    rw [hρ]
    exact hΦ.2 _ (hloc k hk) g
  have hΨ := GlobalTheory.LFun.SatCompare.heckeVec_mem_fixed (Formalism.UG.Final.GLintComm E w n) hh hfix
  rw [hR] at hΨ
  have hΨ' := GlobalTheory.LGrp.mem_fixed.1 hΨ
  have hev : ∀ g, (∑ y ∈ R, ρ y Φ) g = ∑ y ∈ R, Φ (g * loc hw y) := fun g => by
    rw [Finset.sum_apply]
    rfl
  refine ⟨fun γ g => ?_, fun k hk g => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, mul_assoc]
      exact Finset.sum_congr rfl fun y _ => hΦ.1 γ _
  · have hx : comp w k ∈ KGL w (n := n) := (mem_lev.1 hk).2.2 w hS hcS
    set x := comp w k with hxdef
    set k' := (loc hw x)⁻¹ * k with hk'def
    have hk'm : k' ∈ lev S Kw := (lev S Kw).mul_mem ((lev S Kw).inv_mem (hloc x hx)) hk
    have hk'1 : comp w k' = 1 := by
      rw [hk'def, map_mul, map_inv, comp_loc, ← hxdef, inv_mul_cancel]
    have hcomm := (hC E n w hw).1 k' hk'1
    have hkk : k = loc hw x * k' := by rw [hk'def, mul_inv_cancel_left]
    have e1 : ∀ y, Φ (g * k * loc hw y) = Φ (g * loc hw x * loc hw y) := fun y => by
      calc Φ (g * k * loc hw y) = Φ (g * loc hw x * loc hw y * k') := by
            rw [hkk, mul_assoc g, mul_assoc _ k', hcomm y]; simp only [mul_assoc]
        _ = _ := hΦ.2 _ hk'm _
    have e2 := congrFun (hΨ' x hx) g
    rw [hρ, hev, hev] at e2
    show ∑ y ∈ R, Φ (g * k * loc hw y) = ∑ y ∈ R, Φ (g * loc hw y)
    rw [← e2]
    exact Finset.sum_congr rfl fun y _ => e1 y

theorem pHeckePres_of (hC : LocComm) (hM : LocMem) : HeckePres := by
  intro E _ _ _ n w hw ϖ hϖ i
  have hh := GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ i
  obtain ⟨R, hR⟩ := hecke_eq_sum (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ i) (fun g hg => tj_one g hg)
    (Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) hh.2)
  exact ⟨R, hR, fun S Kw hS hcS V _ _ ξ Φ hΦ => sum_mem_forms hC hM hw hh hR hS hcS hΦ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntCompact
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem isCompact_ZU : IsCompact (ZU : Set AfQˣ) := by
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles ℚ
  have hB' : IsCompact (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) : Set AfQᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hO
  have e : (ZU : Set AfQˣ) = Units.embedProduct _ ⁻¹'
      ((GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) ×ˢ
        (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ))) := by
    ext s
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, MulOpposite.unop_op,
      GroundTheory.Global.mem_integralFiniteAdeles]
    constructor
    · intro h
      have h2 := (ZU.inv_mem h)
      exact ⟨fun v => (h v).le, fun v => (h2 v).le⟩
    · rintro ⟨h1, h2⟩ v
      have h3 : Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) = 1 := by
        rw [← map_mul]
        show Valued.v (((s : AfQ) * (↑s⁻¹ : AfQ)) v) = 1
        rw [Units.mul_inv]; exact map_one _
      refine le_antisymm (h1 v) ?_
      calc (1 : _) = Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) := h3.symm
        _ ≤ Valued.v ((s : AfQ) v) * 1 := mul_le_mul_right (h2 v) _
        _ = _ := mul_one _
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hO.prod hB')

private theorem isClosed_GUf (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    IsClosed (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) := by
  have hl : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      (p.1.val.map (conjFin (GlobalTheory.SplitPts.conjE E)))ᵀ * p.1.val :=
    ((Units.continuous_val.comp continuous_fst).matrix_map (continuous_conjFin _)).matrix_transpose.matrix_mul
      (Units.continuous_val.comp continuous_fst)
  have hr : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ) • (1 : Matrix (Fin n) (Fin n) (Af E)) :=
    Continuous.smul (f := fun p : GL (Fin n) (Af E) × AfQˣ => GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ))
      (g := fun _ => (1 : Matrix (Fin n) (Fin n) (Af E)))
      (GroundTheory.Global.AdeleBaseChange.continuous_finiteAdeleMap.comp (Units.continuous_val.comp continuous_snd))
      continuous_const
  exact isClosed_eq hl hr

theorem UpperTheory.Gal.CertificateRingHomMap.pIntCompact_of :
    UpperTheory.Gal.CertificateRingHomMap.IntCompact := by
  intro E _ _ _ n
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have e : Subtype.val '' (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n)) =
      (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) ∩ ((GlobalTheory.EulerTw.Kglob E n : Set _) ×ˢ (ZU : Set AfQˣ)) := by
    ext p
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨h1, -, h3⟩ := mem_lev.1 hk
      exact ⟨k.2, GlobalTheory.EulerTwRestr.mem_Kglob.2 fun w => h3 w (by simp) (by simp), h1⟩
    · rintro ⟨hp, h1, h2⟩
      refine ⟨⟨p, hp⟩, mem_lev.2 ⟨h2, by simp, fun w _ _ => GlobalTheory.EulerTwRestr.mem_Kglob.1 h1 w⟩, rfl⟩
  rw [e]
  exact ((GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).prod isCompact_ZU).inter_left (isClosed_GUf E n)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntSim
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

open GroundTheory.Global.AdeleBaseChange in
private theorem rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ)) • (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := mem_Sim.1 k.2
  have h2 := congrArg (RingHom.mapMatrix (pLoc E u)) h
  rw [map_mul] at h2
  refine Eq.trans ?_ (h2.trans ?_)
  · congr 1
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [RingHom.mapMatrix_apply, sim, Matrix.one_apply]
    · simp [RingHom.mapMatrix_apply, sim, Matrix.one_apply, hij]

open GroundTheory.Global.AdeleBaseChange in
private theorem val_le {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 0 < n) (k : GUf E n)
    (hk : ∀ w, comp w k ∈ GlobalTheory.LFun.KGL w (n := n)) (u : Plc E) :
    Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) ≤ 1 := by
  have h := congrFun (congrFun (rel k u) ⟨0, hn⟩) ⟨0, hn⟩
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  rw [← h]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul, Matrix.transpose_apply, Matrix.map_apply, (conjLoc_spec _ u).2.2]
  exact mul_le_one' (((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val _ _).1 (hk _)).1 _ _)
    (((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val _ _).1 (hk _)).1 _ _)

open GroundTheory.Global.AdeleBaseChange in
theorem UpperTheory.Gal.CertificateRingHomMap.pIntSim_of :
    UpperTheory.Gal.CertificateRingHomMap.IntSim := by
  intro E _ _ _ n hn k hk v
  obtain ⟨P, hPm, hPo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  let u : Plc E := ⟨P, hPm.isPrime, hP0⟩
  have hu : below ℚ u = v := (below_eq_iff u v).2 hPo
  subst hu
  have h1 := val_le hn k hk u
  have h2 := val_le hn k⁻¹ (fun w => by rw [map_inv]; exact inv_mem (hk w)) u
  have hmul : pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ)) * pLoc E u (finiteAdeleMap ℚ E (sim k⁻¹ : AfQˣ)) = 1 := by
    rw [← map_mul, ← map_mul, map_inv, Units.mul_inv, map_one, map_one]
  have h3 : Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : _) = Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) *
          Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k⁻¹ : AfQˣ))) := by
            rw [← map_mul, hmul, map_one]
      _ ≤ Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  have h4 : Valued.v (GroundTheory.Global.SemiLocal.completionMap (below ℚ u) u (((sim k : AfQˣ) : AfQ) (below ℚ u))) = 1 := h3
  rw [GroundTheory.Global.SemiLocal.valued_completionMap] at h4
  exact (pow_eq_one_iff.1 h4).resolve_right (Ideal.ramificationIdx_pos (R := 𝓞 ℚ) u.asIdeal).ne'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLevCompact
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pLevCompact_of :
    UpperTheory.Gal.CertificateRingHomMap.IntCompact → UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.LevOpen → UpperTheory.Gal.CertificateRingHomMap.LevCompact := by
  intro hC hI hL hO E _ _ _ n Up w₀ hw₀ S Kw hS
  obtain ⟨-, hAp, -, -, -, -⟩ := hL E n w₀ hw₀
  have hclosed : IsClosed (lev S Kw : Set (GUf E n)) :=
    Subgroup.isClosed_of_isOpen _ (hO E n S Kw hS.opn)
  have hK₁ := hC E n
  have hJ := hS.cpt w₀ hS.mem
  have hKo := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w₀ n).1
  obtain ⟨F, -, hF⟩ := hJ.elim_nhds_subcover
    (fun a => {y : GLw n w₀ | a⁻¹ * y ∈ GlobalTheory.LFun.KGL w₀ (n := n)}) (fun a _ => by
      refine IsOpen.mem_nhds (hKo.preimage (continuous_const.mul continuous_id)) ?_
      simp [Subgroup.one_mem])
  have hcov : IsCompact (⋃ a ∈ F, (fun x : GUf E n => loc hw₀ a * x) ''
      (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n))) :=
    F.isCompact_biUnion fun a _ => hK₁.image (continuous_const.mul continuous_id)
  refine hcov.of_isClosed_subset hclosed fun k hk => ?_
  obtain ⟨hsim, hmem, hoff⟩ := mem_lev.1 hk
  obtain ⟨a, haF, ha⟩ := Set.mem_iUnion₂.1 (hF (hmem w₀ hS.mem))
  have ha' : a⁻¹ * comp w₀ k ∈ GlobalTheory.LFun.KGL w₀ (n := n) := ha
  have hsim' : sim ((loc hw₀ a)⁻¹ * k) ∈ ZU := by simpa using hsim
  have hw : comp w₀ ((loc hw₀ a)⁻¹ * k) ∈ GlobalTheory.LFun.KGL w₀ (n := n) := by simpa using ha'
  have hint : ∀ u : Plc E, u ≠ w₀ → u ≠ cj w₀ → comp u k ∈ GlobalTheory.LFun.KGL u (n := n) := by
    intro u h1 h2
    have hcc : cj (cj u) = u := GlobalTheory.SplitPts.conjSrc_conjSrc_cm u
    by_cases hu : u ∈ S
    · exact hS.le u hu h1 (hmem u hu)
    by_cases hc : cj u ∈ S
    · have hne : cj u ≠ w₀ := fun h => h2 (by rw [← h, hcc])
      have := hI E n k (cj u) hsim (hS.le _ hc hne (hmem _ hc))
      rwa [hcc] at this
    · exact hoff u hu hc
  have hk' : (loc hw₀ a)⁻¹ * k ∈ lev (E := E) (n := n) ∅ (fun _ => ⊤) := by
    refine mem_lev.2 ⟨hsim', by simp, fun u _ _ => ?_⟩
    by_cases h1 : u = w₀
    · subst h1; exact hw
    by_cases h2 : u = cj w₀
    · subst h2; exact hI E n _ w₀ hsim' hw
    · have happ : GlobalTheory.Cong.Apart u w₀ := (hAp u).2 ⟨h1, h2⟩
      have : comp u ((loc hw₀ a)⁻¹ * k) = comp u k := by
        rw [map_mul, map_inv, comp_loc_of_apart hw₀ happ, inv_one, one_mul]
      rw [this]
      exact hint u h1 h2
  exact Set.mem_iUnion₂.2 ⟨a, haF, _, hk', by simp⟩
end

