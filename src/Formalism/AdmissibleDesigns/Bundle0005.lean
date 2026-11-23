module

public import Formalism.AdmissibleDesigns.LengthSemilinear
public import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointCondH0W
public import Formalism.AdmissibleDesigns.CoboundaryMemFiniteClasses
public import Formalism.AdicCompletionExports.AdicCompleteRingEquiv.IsAdicCompleteOfRingEquiv
public import Formalism.AdmissibleDesigns.MemImageOfTensorSum
public import Formalism.AdmissibleDesigns.ExistsWildInertiaCyclotomicGenerator
public import Formalism.AdmissibleDesigns.TrCMemZ1D

@[expose] public section

-- bundled from Formalism.AdmissibleDesigns.BkLocCol
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N.KHf

section Col

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) {A T' : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A]
  (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
  (r : GE D.nd →* A) (χ : GE D.nd →* T'ˣ)
  (φ : M ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r)
  (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := M) r χ g m) = Br.WKO i ρ π g (φ m))


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem bkLoc_col (n : ℕ) (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    (ρV : Representation (D.nd.O i) ↥(decs D.host.E (Aw i dc) n) V) (qV : V →ₗ[D.nd.O i] M)
    (Ψ : TrV (eK (D.nbr i _ hw)) V →ₗ[Br.LLw (D.nbr i _ hw)] (Fin D.R.r → Br.LLw (D.nbr i _ hw)))
    (hΨc : Continuous Ψ)
    (hΨe : ∀ g v, Ψ (repL (eK (D.nbr i _ hw)) ρV (Br.iota D.nbr i _ hw) g v) =
      matRep (Br.locM (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g (Ψ v))
    (hcomp : ∀ v, Br.phi (D.nbr i _ hw) D.R.r (φ (qV v)) = Submodule.Quotient.mk (Ψ v))
    (y : ReciprocityTheory.Gal.H1 ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))))
    (hy : psi (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
        ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) y ∈
      F0col i dc n ρV (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n)) qV) :
    y ∈ Br.bk D.loc D.nbr i (plOf i dc n) hw (WpO D.nd i ρ π) := by
  induction y using Submodule.Quotient.induction_on with
  | H f =>
    have hy' : Submodule.Quotient.mk (psiZ (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
        ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) f) ∈
        F0col i dc n ρV (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n)) qV := hy
    obtain ⟨c, hc, hceq⟩ := Submodule.mem_map.mp hy'
    have hd := (Submodule.Quotient.eq _).1 hceq
    have hpsi := Submodule.sub_mem _ hc (Submodule.mem_sup_right hd)
    simp only [Submodule.mem_comap, Submodule.coe_subtype, sub_sub_cancel] at hpsi
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hpsi
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨m, rfl⟩ := hb
    have hz' : z ∈ fZ i dc n ρV := hz
    unfold fZ at hz'
    rw [dite_eq_left hw] at hz'
    have hz2 : (fun g => (z (Br.iota D.nbr i _ hw g) : TrV (eK (D.nbr i _ hw)) V)) ∈
        finiteCocycles (Br.PD D.loc D.nbr i _ hw) (repL (eK (D.nbr i _ hw)) ρV (Br.iota D.nbr i _ hw)) := hz'
    have hpt : ∀ x, f.1 x = φ (qV (z x)) + ((Br.WKO i ρ π) (x : GE D.nd) (φ m) - φ m) := by
      intro x
      have e := congrFun hab x
      change qV (z x) + (uRep (D.nd.O i) (M := M) r χ (x : GE D.nd) m - m) = φ.symm (f.1 x) at e
      rw [← hφ, ← map_sub, ← map_add (f := _), e, LinearEquiv.apply_symm_apply]
    have h1 : (fun g => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g))) :
        ↥(GK (D.nbr i _ hw).Kw) → (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T) ∈
        HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) :=
      Submodule.mem_sup_left ⟨fun g => Ψ (z (Br.iota D.nbr i _ hw g)),
        (cocyclesFunctorial_holds _ _ _ _ _ _ _ _ _ _ _ _ Ψ hΨc hΨe _).2 hz2, rfl⟩
    have h2 : (fun g => actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
          (Br.phi (D.nbr i _ hw) D.R.r (φ m)) - (show (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸ (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T from
            Br.phi (D.nbr i _ hw) D.R.r (φ m))) ∈
        HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) :=
      Submodule.mem_sup_right ⟨Br.phi (D.nbr i _ hw) D.R.r (φ m), rfl⟩
    have h3 := Submodule.add_mem _ h1 h2
    have hfun : (Br.Phi (D.nbr i _ hw) ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) f :
        ↥(GK (D.nbr i _ hw).Kw) → (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T) =
        (fun g => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g)))) +
        (fun g => actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
          (Br.phi (D.nbr i _ hw) D.R.r (φ m)) - (show (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸ (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T from
            Br.phi (D.nbr i _ hw) D.R.r (φ m))) := by
      funext g
      have hact : Br.phi (D.nbr i _ hw) D.R.r (Br.WKO i ρ π (Br.ι (D.nbr i _ hw) g : GE D.nd) (φ m)) =
          actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
            (Br.phi (D.nbr i _ hw) D.R.r (φ m)) :=
        phi_act D i (plOf i dc n) hw ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n))) g (φ m)
      show Br.phi (D.nbr i _ hw) D.R.r (f.1 (Br.ι (D.nbr i _ hw) g)) = _
      rw [hpt, map_add (f := _), map_sub, hcomp]
      exact congrArg (fun t => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g))) +
        (t - Br.phi (D.nbr i _ hw) D.R.r (φ m))) hact
    have hmem : f ∈ (HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
        (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n))))).comap
          (Br.Phi (D.nbr i _ hw) ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n)))) := by
      exact Submodule.mem_comap.mpr (hfun ▸ h3)
    exact ⟨f, hmem, rfl⟩

end Col

end Formalism.MainNotions.N.K.Sel

end
end

-- bundled from Formalism.AdmissibleDesigns.CycMatchRec
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Classical

namespace Formalism.MainNotions.N.KBKa

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.MainNotions.N.KHf

section Cyc

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycZ_eq_χQ (g : ↥(GK Bw.Kw)) :
    ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) : ℚ_[l]) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := by
  set x : ℚ_[l] := ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) : ℚ_[l])
    with hx
  set x' : ℚ_[l] := ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) with hx'
  have key : ∀ m : ℕ, ‖x - x'‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    haveI : NeZero ((l ^ m : ℕ) : Ω) := ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    obtain ⟨ζ', hζ'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hζ : IsPrimitiveRoot (Bw.j ζ') (l ^ m) := hζ'.map_of_injective Bw.j.injective
    obtain ⟨a, ha, hxa⟩ := Formalism.AdicCompletionExports.isCycG_cycZ l E Ω ℤ_[l] (RingHom.id _)
      ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) m ζ' hζ'.pow_eq_one
    obtain ⟨a', hxa', ha'⟩ := P.χQ_cyc (g : GQ l) m (Bw.j ζ') hζ.pow_eq_one
    have hg : (g : GQ l) (Bw.j ζ') = Bw.j ζ' ^ a := by
      have h0 := Bw.e_comm (Br.ι Bw g) ζ'
      have he : Bw.e (Br.ι Bw g) = g := Bw.e.apply_symm_apply g
      rw [he] at h0
      rw [h0, ha, map_pow]
    have h1 : a ≡ a' [MOD l ^ m] := by
      have h0 := hg.symm.trans ha'
      have hf : IsOfFinOrder (Bw.j ζ') :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ m, pow_pos (Fact.out : l.Prime).pos m, hζ.pow_eq_one⟩
      rwa [hf.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h0
    have hxa2 : ‖x - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      change ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) - (a : ℤ_[l]))
        ∈ Ideal.span {(l : ℤ_[l]) ^ m} at hxa
      have h0 := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hxa
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h0
      exact h0
    have h2 : ‖((a : ℚ_[l]) - (a' : ℚ_[l]))‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      have h3 : ((l ^ m : ℕ) : ℤ) ∣ (a : ℤ) - (a' : ℤ) := Nat.modEq_iff_dvd.1 h1.symm
      have h4 := (Padic.norm_int_le_pow_iff_dvd ((a : ℤ) - a') m).2 (by exact_mod_cast h3)
      simpa using h4
    have h4 : x - x' = (x - a) + ((a - a') + -(x' - a')) := by ring
    rw [h4]
    exact (Padic.nonarchimedean _ _).trans (max_le hxa2 ((Padic.nonarchimedean _ _).trans
      (max_le h2 (by rwa [norm_neg]))))
  have hlim : Filter.Tendsto (fun m : ℕ => (l : ℝ) ^ (-(m : ℤ))) Filter.atTop (nhds 0) := by
    have h5 : ∀ m : ℕ, (l : ℝ) ^ (-(m : ℤ)) = ((l : ℝ)⁻¹) ^ m := fun m => by
      rw [zpow_neg, zpow_natCast, inv_pow]
    simp only [h5]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt))
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' hlim key))

end Cyc

section TopPi

variable {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace (FractionRing O)]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  (n : Type) [Fintype n]

end TopPi

section RecC

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  {VT VT' : Type}
  [AddCommGroup VT] [Module (D.nd.O i) VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul (D.nd.O i) VT] [Module (FractionRing (D.nd.O i)) VT]
  [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VT]
  [AddCommGroup VT'] [Module (D.nd.O i) VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul (D.nd.O i) VT'] [Module (FractionRing (D.nd.O i)) VT']
  [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VT']

theorem cycMatch_rec {w : ℕ} (hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i))
    (Dw : Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) VT VT')
    (hε : ∀ g : ↥(Γn i dc w), Dw.ε g = epsU D.nd i (g : GE D.nd)) :
    CycMatch Dw (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) (Br.PD D.loc D.nbr i _ hn) := by
  intro g
  rw [hε]
  have hP := cycZ_eq_χQ (D.nbr i _ hn) (D.loc (D.nd.l i)) g
  have hχ := (D.loc (D.nd.l i)).PD_χ (D.nbr i _ hn).Kw g
  simp only [eK, RingEquiv.ofBijective_apply, Br.toLLK, IsFractionRing.lift_algebraMap, LocBridge.toLL,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, epsU, Glob.epsO, MonoidHom.comp_apply,
    Units.coe_map, MonoidHom.coe_coe, cycLL, Br.PD, RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    LocBridge.eO_alg]
  rw [← IsScalarTower.algebraMap_apply, hχ, ← hP]
  first
  | exact IsScalarTower.algebraMap_apply ℤ_[D.nd.l i] ℚ_[D.nd.l i] _ _
  | rfl

end RecC

section RecD

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))

theorem rowIn_of {w : ℕ} (hε : ∀ g : ↥(Γn i dc w), (Dat w).ε g = epsU D.nd i (g : GE D.nd))
    (ht : ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
      HomeoK (eK (D.nbr i _ hn)) ∧ TopMatch (eK (D.nbr i _ hn)) (VT w) ∧ TopMatch (eK (D.nbr i _ hn)) (VT' w))
    (hdr : ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
      IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn)) (Dat w).ρT (Br.iota D.nbr i _ hn))) :
    RowIn i dc VT VT' Dat w := by
  intro hn
  obtain ⟨h1, h2, h3⟩ := ht hn
  exact ⟨h1, h2, h3, cycMatch_rec i dc hn (Dat w) hε, hdr hn⟩

end RecD

end Formalism.MainNotions.N.KBKa
end
end

-- bundled from Formalism.AdmissibleDesigns.ExistsUnrDec
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N

section Gen

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem exists_unr_dec (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ χ : ↥(A.decompositionSubgroup F) → ℤ_[p], Continuous χ ∧ (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : ↥(A.decompositionSubgroup F), (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A → χ g = 0) ∧ ∃ g, χ g = 1 := by
  exact hT2Core.out.unr A hp

end Gen

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

private lemma plOf_colIdx (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) = l.1 := by
  have hmem : l.1 ∈ K.plSet i dc := by
    simp only [K.plSet, Finset.mem_union]
    exact Or.inl (Or.inr l.2)
  have hlt : ((K.plSet i dc).equivFin ⟨l.1, hmem⟩ : ℕ) < (K.plSet i dc).card := Fin.is_lt _
  unfold K.colIdx K.idx K.plOf
  rw [dite_eq_left hmem, dite_eq_left hlt]
  simp

theorem col_over (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ placesOver D.host.E (D.nd.l i) := by
  rw [plOf_colIdx]
  first
  | exact (dc.cover l.1).mp (Or.inr l.2)
  | exact ((dc.cover l.1).mp (Or.inr l.2)).1
  | (have h := (dc.cover l.1).mp (Or.inr l.2); done)

theorem col_hp (l : K.Col i dc) :
    (K.Aw i dc (K.colIdx i dc l)).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 := by
  have hov := col_over i dc l
  rw [plOf_colIdx] at hov
  unfold K.Aw
  rw [plOf_colIdx]
  have h2 := (D.nd.plOm.2 l.1 ((D.nd.l i : ℕ) : 𝓞 D.host.E)).mpr hov
  simpa using h2

theorem unrHom (l : K.Col i dc) : KFin.UnrHom i dc l := by
  obtain ⟨χ, hc, hm, hI, g1, h1⟩ :=
    exists_unr_dec (F := D.host.E) (K.Aw i dc (K.colIdx i dc l)) (col_hp i dc l)
  refine ⟨fun g => algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g), ⟨fun g h => ?_, fun g hg => ?_, fun hn => ?_⟩, g1, ?_⟩
  · show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ (g * h)) = _ + _
    rw [hm, map_add (f := _)]
  · have hg' : ((g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om)) ∈ Ine (F := D.host.E) (K.Aw i dc (K.colIdx i dc l)) :=
      Subgroup.mem_subgroupOf.1 hg
    show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g) = 0
    rw [hI g hg', map_zero]
  · have hf : Continuous fun g : ↥(KFin.Γc i dc l) => algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g) :=
      (K.Topo.continuous_alg i).comp hc
    have e1 : ∀ c : D.nd.O i, KHf.eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) =
        ((D.nbr i _ hn).eO c : Br.LLw (D.nbr i _ hn)) := fun c => by
      rw [KHf.eK_apply, Br.toLLK_alg]
      rfl
    simp only [e1]
    exact continuous_subtype_val.comp ((D.nbr i _ hn).eO_cont.comp (hf.comp (Br.iota_cont D.nbr i _ hn)))
  · show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g1) = 1
    rw [h1, map_one]

end Rec

end Formalism.MainNotions.N.KUnr
end
end

-- bundled from Formalism.AdmissibleDesigns.MemUnramifiedOfCoboundary
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {O' : Type} [CommRing O'] {σ : O' ≃+* O}
    {A T' GG : Type} [Ring A] [Algebra O' A] [CommRing T'] [Algebra T' A] [Group GG]
    {M : Type} [AddCommGroup M] [Module A M] [Module O' M] [SMulCommClass A O' M]
    {r : GG →* A} {χ : GG →* T'ˣ} {E : A} {Dw : Subgroup GG} {eG : Dw ≃* G}

theorem back_cob {e cB ℓ : ℕ} (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hp : PD.p = ℓ) (z : Dw → M)
    (x : Cd.Ce.V ⧸ Cd.Ce.L.T) (g : Dw)
    (hg : (((PD.p : O) ^ cB) • trC Cd z) (eG g) = actD Cd.Ce.L (eG g) x - x) :
    ((ℓ : O') ^ cB) • z g = uElt r χ (g : GG) • Cd.u.symm x - Cd.u.symm x := by
  apply Cd.u.injective
  rw [map_sub, Cd.u_act, AddEquiv.apply_symm_apply, Cd.u_smul, map_pow, map_natCast, ← hg, ← hp]
  simp only [trC, MulEquiv.symm_apply_apply, Pi.smul_apply]

theorem tb_pos {e t cB ℓ : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (he : 0 < e) (het : e < t)
    (Y : YtLat (G := G) (Qp := Qp) LL O) (hY : YtCrys (PD := PD) Y J)
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hψ : PsiExt σ r χ E Dw eG Y Cd) [TopologicalSpace Dw]
    (hloc : YLoc (O := O') M r χ E Dw) (heG : Continuous eG.symm) (hp : PD.p = ℓ)
    (ψ : Ymod r χ E →ₗ[O'] M) (hψe : ∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : ∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : GG))) :
    ((ℓ : O') ^ cB) • (z : Dw → M) ∈ coB1 (resRep (uRep O' (M := M) r χ) Dw) := by
  have hzl : IsLocallyConstant (z : Dw → M) := by
    have h := hloc ψ hψe
    have hf : (z : Dw → M) = fun g : Dw => ψ (yY r χ E (g : GG)) := funext hz
    rw [hf]
    exact h
  have h1 := trC_hf hTB het Y hY Cd hψ ψ hψe (z : Dw → M) hz
  have h2 := trC_mem_Z1D Cd heG z hzl ((PD.p : O) ^ cB)
  obtain ⟨x, hx⟩ := (hTB.2 e het Cd.Ce.V Cd.Ce.ρ Cd.Ce.L Cd.Ce.cont Cd.Ce.mat).1 he ⟨h2, h1⟩
  refine ⟨Cd.u.symm x, ?_⟩
  funext g
  show uElt r χ (g : GG) • Cd.u.symm x - Cd.u.symm x = ((ℓ : O') ^ cB) • (z : Dw → M) g
  refine (back_cob Cd hp (z : Dw → M) x g ?_).symm
  have := congrFun hx (eG g)
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at this
  exact this.symm

theorem tb_zero {e t cB ℓ : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (he : e = 0) (het : e < t)
    (Y : YtLat (G := G) (Qp := Qp) LL O) (hY : YtCrys (PD := PD) Y J)
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hψ : PsiExt σ r χ E Dw eG Y Cd) [TopologicalSpace Dw]
    (hloc : YLoc (O := O') M r χ E Dw) (heG : Continuous eG.symm) (hp : PD.p = ℓ)
    (I' : Subgroup Dw) (hI : ∀ g : Dw, g ∈ I' → eG g ∈ I)
    (ψ : Ymod r χ E →ₗ[O'] M) (hψe : ∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : ∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : GG))) :
    IsLocallyConstant (z : Dw → M) ∧
    ∃ m : M, ∀ g : Dw, g ∈ I' → ((ℓ : O') ^ cB) • (z : Dw → M) g = uElt r χ (g : GG) • m - m := by
  have hzl : IsLocallyConstant (z : Dw → M) := by
    have h := hloc ψ hψe
    have hf : (z : Dw → M) = fun g : Dw => ψ (yY r χ E (g : GG)) := funext hz
    rw [hf]
    exact h
  refine ⟨hzl, ?_⟩
  have h1 := trC_hf hTB het Y hY Cd hψ ψ hψe (z : Dw → M) hz
  have h2 := trC_mem_Z1D Cd heG z hzl ((PD.p : O) ^ cB)
  have hmem : ((PD.p : O) ^ cB) • trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L := ⟨h2, h1⟩
  rw [(hTB.2 e het Cd.Ce.V Cd.Ce.ρ Cd.Ce.L Cd.Ce.cont Cd.Ce.mat).2.1 he] at hmem
  obtain ⟨a, ⟨x, hx⟩, b, ⟨y, hy⟩, hab⟩ := Submodule.mem_sup.1 hmem.2
  refine ⟨Cd.u.symm (x + y), fun g hg => back_cob Cd hp (z : Dw → M) (x + y) g ?_⟩
  have hb := congrFun hy (eG g)
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at hb
  rw [← hab, Pi.add_apply, hx (eG g) (hI g hg), ← hb, map_add (f := _)]
  abel

end Transport

section Cls

variable {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M] (ρ : Representation O Γ M)

theorem mkQ_eq_zero_of (z : coZ1s ρ) (h : (z : Γ → M) ∈ coB1 ρ) :
    (Submodule.mkQ _ z : H1z ρ) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr h

theorem mem_unramified_of_coboundary (I : Subgroup Γ) (z : coZ1s ρ) (m : M) (hm : ∀ g ∈ I, (z : Γ → M) g = ρ g m - m) :
    (Submodule.mkQ _ z : H1z ρ) ∈ unrH1 ρ I := by
  rw [unrH1, LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨m, ?_⟩
  funext g
  exact (hm g.1 g.2).symm

theorem mem_locally_constant_of [TopologicalSpace Γ] (z : coZ1s ρ) (h : IsLocallyConstant (z : Γ → M)) :
    (Submodule.mkQ _ z : H1z ρ) ∈ Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 ρ :=
  ⟨z, h, rfl⟩

end Cls

end Formalism.MainNotions.N.K.TB

end
end

