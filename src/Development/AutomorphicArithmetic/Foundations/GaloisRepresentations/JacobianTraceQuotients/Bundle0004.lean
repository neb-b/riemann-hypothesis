module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.LocDescOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0042

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.SubPerm
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.LocGL
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.subPerm :
    UpperTheory.Gal.Join.SubPerm := by
  intro k _ _ _ _ n V _ _ π hi ω hω w h
  have hw : ∀ i, IsSmoothChar ((ω ∘ w) i) := fun i => hω (w i)
  have h1 := (UpperTheory.Gal.LocD.ofSupport k n V π ω hω).2 ⟨hi, h⟩
  have e : (Finset.univ.val.map fun i => IrrGL.ofChar ((ω ∘ w) i) (hw i)) =
      Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i) := by
    have e' := congrArg (Multiset.map fun i => IrrGL.ofChar (ω i) (hω i)) (Multiset.map_univ_val_equiv w)
    rw [Multiset.map_map] at e'
    exact e'
  rw [← e] at h1
  exact ((UpperTheory.Gal.LocD.ofSupport k n V π (ω ∘ w) hw).1 h1).2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.SubQuot
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem jointEig {ι V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : ι → Module.End ℂ V) (c : ι → ℂ) (hc : ∀ i j, Commute (f i) (f j))
    (h : (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) ≠ ⊥) :
    ∃ y, y ≠ 0 ∧ ∀ i, f i y = c i • y := by
  classical
  have hcN : ∀ i j, Commute (f i) (f j - c j • (1 : Module.End ℂ V)) := fun i j =>
    (hc i j).sub_right ((Commute.one_right _).smul_right _)
  have hW_inv : ∀ i, ∀ u ∈ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V),
      f i u ∈ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) := by
    intro i u hu
    rw [Module.End.mem_iInf_maxGenEigenspace_iff] at hu ⊢
    intro j
    obtain ⟨k, hk⟩ := hu j
    refine ⟨k, ?_⟩
    rw [← Module.End.mul_apply, ← ((hcN i j).pow_right k).eq, Module.End.mul_apply, hk, map_zero]
  have hex : ∃ n, ∃ U : Submodule ℂ V, U ≠ ⊥ ∧
      U ≤ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) ∧
      (∀ i, ∀ u ∈ U, f i u ∈ U) ∧ Module.finrank ℂ U = n :=
    ⟨_, _, h, le_rfl, hW_inv, rfl⟩
  obtain ⟨U, hU0, hUW, hUinv, hUn⟩ := Nat.find_spec hex
  have hker : ∀ i, ∀ u ∈ U, f i u = c i • u := by
    intro i
    have hNU : ∀ m : ℕ, ∀ u ∈ U, ((f i - c i • (1 : Module.End ℂ V)) ^ m) u ∈ U := by
      intro m
      induction m with
      | zero => intro u hu; simpa using hu
      | succ m ih =>
        intro u hu
        rw [pow_succ', Module.End.mul_apply]
        have hv := ih u hu
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
        exact U.sub_mem (hUinv i _ hv) (U.smul_mem _ hv)
    let K : Submodule ℂ V := U ⊓ LinearMap.ker (f i - c i • (1 : Module.End ℂ V))
    have hKinv : ∀ j, ∀ u ∈ K, f j u ∈ K := by
      intro j u hu
      refine ⟨hUinv j u hu.1, ?_⟩
      have h2 : (f i - c i • (1 : Module.End ℂ V)) u = 0 := hu.2
      show (f i - c i • (1 : Module.End ℂ V)) (f j u) = 0
      rw [← Module.End.mul_apply, ← (hcN j i).eq, Module.End.mul_apply, h2, map_zero]
    have hK0 : K ≠ ⊥ := by
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have hexk : ∃ k, ((f i - c i • (1 : Module.End ℂ V)) ^ k) u = 0 :=
        (Module.End.mem_iInf_maxGenEigenspace_iff f c u).mp (hUW huU) i
      obtain ⟨k, hk, hkmin⟩ : ∃ k, ((f i - c i • (1 : Module.End ℂ V)) ^ k) u = 0 ∧
          ∀ m < k, ((f i - c i • (1 : Module.End ℂ V)) ^ m) u ≠ 0 :=
        ⟨Nat.find hexk, Nat.find_spec hexk, fun m hm => Nat.find_min hexk hm⟩
      have hk0 : k ≠ 0 := by
        rintro rfl
        simp at hk
        exact hu0 hk
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      refine (Submodule.ne_bot_iff K).mpr ⟨((f i - c i • (1 : Module.End ℂ V)) ^ m) u,
        ⟨hNU m u huU, ?_⟩, hkmin m (Nat.lt_succ_self m)⟩
      show (f i - c i • (1 : Module.End ℂ V)) (((f i - c i • (1 : Module.End ℂ V)) ^ m) u) = 0
      rw [← Module.End.mul_apply, ← pow_succ']
      exact hk
    have hle : Nat.find hex ≤ Module.finrank ℂ K :=
      Nat.find_min' hex ⟨K, hK0, le_trans inf_le_left hUW, hKinv, rfl⟩
    have hKU : K = U := Submodule.eq_of_le_of_finrank_eq inf_le_left
      (le_antisymm (Submodule.finrank_mono inf_le_left) (hUn ▸ hle))
    intro u hu
    have hu' : u ∈ K := hKU ▸ hu
    have h3 : (f i - c i • (1 : Module.End ℂ V)) u = 0 := hu'.2
    simpa [sub_eq_zero] using h3
  obtain ⟨y, hyU, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  exact ⟨y, hy0, fun i => hker i y hyU⟩

theorem UpperTheory.Gal.Join.subQuot :
    UpperTheory.Gal.Join.SubQuot := by
  intro T X _ _ _ _ ρ μ
  have hc : ∀ s t : T, Commute (ρ s) (ρ t) := fun s t => by
    show ρ s * ρ t = ρ t * ρ s
    rw [← map_mul, ← map_mul, mul_comm]
  have iff1 : (∃ y, y ≠ 0 ∧ ∀ t : T, ρ t y = (μ t : ℂ) • y) ↔
      (⨅ t, Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) : Submodule ℂ X) ≠ ⊥ := by
    constructor
    · rintro ⟨y, hy0, hy⟩
      refine (Submodule.ne_bot_iff _).mpr ⟨y, ?_, hy0⟩
      rw [Module.End.mem_iInf_maxGenEigenspace_iff]
      intro t
      refine ⟨1, ?_⟩
      simp [hy t]
    · intro h
      exact jointEig (fun t => ρ t) (fun t => (μ t : ℂ)) hc h
  refine ⟨iff1, fun hy => ?_⟩
  have hWne := iff1.mp hy
  let c : T → ℂ := fun t => (μ t : ℂ)
  let Wχ : (T → ℂ) → Submodule ℂ X := fun χ => ⨅ t, Module.End.maxGenEigenspace (ρ t) (χ t)
  let S : Submodule ℂ X := ⨆ χ ∈ {χ : T → ℂ | χ ≠ c}, Wχ χ
  have hind : iSupIndep Wχ :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo _
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  have hdisj : Disjoint (Wχ c) S := hind.disjoint_biSup (fun h => h rfl)
  have htop : Wχ c ⊔ S = ⊤ := by
    have h1 : ⨆ χ : T → ℂ, Wχ χ = ⊤ :=
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo _
        (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
        (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
    refine eq_top_iff.mpr (h1.symm.le.trans (iSup_le fun χ => ?_))
    by_cases hχ : χ = c
    · subst hχ; exact le_sup_left
    · exact le_sup_of_le_right (le_biSup Wχ (show χ ∈ {χ : T → ℂ | χ ≠ c} from hχ))
  have hWinv : ∀ χ t, ∀ x ∈ Wχ χ, ρ t x ∈ Wχ χ := by
    intro χ t x hx
    simp only [Wχ, Submodule.mem_iInf] at hx ⊢
    intro s
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc s t) (χ s) (hx s)
  have hSinv : ∀ t, ∀ x ∈ S, ρ t x ∈ S := by
    intro t
    have : S ≤ S.comap (ρ t) := iSup₂_le fun χ hχ x hx =>
      (le_biSup Wχ hχ) (hWinv χ t x hx)
    exact fun x hx => this hx
  have hNS : ∀ t (k : ℕ), ∀ x ∈ S, ((ρ t - c t • (1 : Module.End ℂ X)) ^ k) x ∈ S := by
    intro t k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      have hv := ih x hx
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact S.sub_mem (hSinv t _ hv) (S.smul_mem _ hv)
  have hSlt : S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun hS => hWne ?_
    have : Disjoint (Wχ c) ⊤ := hS ▸ hdisj
    exact disjoint_top.mp this
  obtain ⟨l0, hl00, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hSlt inferInstance
  let g : T → Module.End ℂ (Module.Dual ℂ X) := fun t => Module.Dual.transpose (R := ℂ) (ρ t)
  have hg : ∀ s t, Commute (g s) (g t) := by
    intro s t
    show g s * g t = g t * g s
    ext φ x
    simp only [Module.End.mul_apply, g, Module.Dual.transpose_apply, LinearMap.comp_apply]
    rw [← Module.End.mul_apply, (hc t s).eq, Module.End.mul_apply]
  have hpow : ∀ t (k : ℕ) (φ : Module.Dual ℂ X),
      ((g t - c t • (1 : Module.End ℂ (Module.Dual ℂ X))) ^ k) φ =
        φ ∘ₗ ((ρ t - c t • (1 : Module.End ℂ X)) ^ k) := by
    intro t k
    induction k with
    | zero => intro φ; ext x; simp
    | succ k ih =>
      intro φ
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ]
      ext x
      simp [g, Module.Dual.transpose_apply, Module.End.mul_apply, smul_eq_mul]
  obtain ⟨l, hl0, hl⟩ := jointEig g c hg (by
    refine (Submodule.ne_bot_iff _).mpr ⟨l0, ?_, hl00⟩
    rw [Module.End.mem_iInf_maxGenEigenspace_iff]
    intro t
    refine ⟨Module.finrank ℂ X, ?_⟩
    rw [hpow]
    ext x
    have hx : x ∈ Wχ c ⊔ S := htop ▸ Submodule.mem_top
    obtain ⟨w, hw, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
    have hw' : w ∈ Module.End.maxGenEigenspace (ρ t) (c t) :=
      (Submodule.mem_iInf _).mp hw t
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker] at hw'
    have hs' : l0 (((ρ t - c t • (1 : Module.End ℂ X)) ^ Module.finrank ℂ X) s) = 0 := by
      have hm := Submodule.mem_map_of_mem (f := l0) (hNS t (Module.finrank ℂ X) s hs)
      rw [hmap] at hm
      exact (Submodule.mem_bot ℂ).mp hm
    simp only [LinearMap.comp_apply, map_add (f := _), hw', map_zero, zero_add, LinearMap.zero_apply]
    exact hs')
  refine ⟨l, hl0, fun t y => ?_⟩
  have := congrArg (fun φ : Module.Dual ℂ X => φ y) (hl t)
  simpa [g, Module.Dual.transpose_apply, smul_eq_mul] using this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceExp
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem lift_eigen {T V : Type} [CommGroup T] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ T V) {ψ μ : T →* ℂˣ} {v y : V} (hψ : ∀ t, ρ t v = (ψ t : ℂ) • v)
    (hne : μ ≠ ψ) (hy : y ∉ Submodule.span ℂ {v})
    (hq : ∀ t, ρ t y - (μ t : ℂ) • y ∈ Submodule.span ℂ {v}) (hv : v ≠ 0) :
    ∃ z, z ≠ 0 ∧ ∀ t, ρ t z = (μ t : ℂ) • z :=
  _root_.UpperTheory.Reformulated.B.R4.lift_eigen ρ hψ hne hy hq hv

private theorem exists_eigenchars {T : Type} [CommGroup T] (d : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ T V), Module.finrank ℂ V = d →
    ∃ E : Multiset (T →* ℂˣ), (∀ t, LinearMap.trace ℂ V (ρ t) = (E.map fun χ => (χ t : ℂ)).sum) ∧
      ∀ μ, μ ∈ E ↔ ∃ y, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y := by
  induction d with
  | zero =>
    intro V _ _ _ ρ h
    haveI : Subsingleton V := Module.finrank_zero_iff.1 h
    refine ⟨0, fun t => ?_, fun μ => ?_⟩
    · simp [Subsingleton.elim (ρ t) 0]
    · simp [Subsingleton.elim _ (0 : V)]
  | succ d ih =>
    intro V _ _ _ ρ h
    haveI : Nontrivial V := Module.finrank_pos_iff.1 (by rw [h]; exact d.succ_pos)
    obtain ⟨ψ, v, hv, hψ⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ T V ρ fun a b => by
      rw [← map_mul, mul_comm, map_mul]
    have hst : ∀ g, Submodule.span ℂ {v} ≤ (Submodule.span ℂ {v}).comap (ρ g) := fun g => by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap, hψ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have hd : Module.finrank ℂ (V ⧸ Submodule.span ℂ {v}) = d := by
      have := (Submodule.span ℂ {v}).finrank_quotient_add_finrank
      rw [finrank_span_singleton hv, h] at this
      omega
    obtain ⟨E, h1, h2⟩ := ih _ (ρ.quotient _ hst) hd
    refine ⟨ψ ::ₘ E, fun t => ?_, fun μ => ⟨fun hμ => ?_, ?_⟩⟩
    · rw [GlobalTheory.IwahoriTraceProof.trace_eq_add_quot (ρ t) hv (hψ t) (ρ.quotient _ hst t) fun _ => rfl, h1,
        Multiset.map_cons, Multiset.sum_cons]
    · by_cases hne : μ = ψ
      · exact ⟨v, hv, hne ▸ hψ⟩
      obtain ⟨q, hq0, hq⟩ := (h2 μ).1 ((Multiset.mem_cons.1 hμ).resolve_left hne)
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine lift_eigen ρ hψ hne (fun hy => hq0 ((Submodule.Quotient.mk_eq_zero _).2 hy)) (fun t => ?_) hv
      refine (Submodule.Quotient.eq _).1 ?_
      exact hq t
    · rintro ⟨y, hy, hμ⟩
      by_cases hne : μ = ψ
      · exact hne ▸ Multiset.mem_cons_self _ _
      refine Multiset.mem_cons_of_mem ((h2 μ).2 ⟨Submodule.Quotient.mk y, fun h0 => hne ?_, fun t => ?_⟩)
      · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
        refine MonoidHom.ext fun t => Units.ext ?_
        have h3 := hμ t
        rw [map_smul, hψ, smul_comm, ← sub_eq_zero, ← sub_smul] at h3
        rcases smul_eq_zero.1 h3 with h3 | h3
        · exact (sub_eq_zero.1 h3).symm
        · exact absurd h3 hy
      · exact congrArg (Submodule.Quotient.mk (p := Submodule.span ℂ {v})) (hμ t)

theorem UpperTheory.Gal.Join.traceExp :
    UpperTheory.Gal.Join.TraceExp := by
  intro T X _ _ _ ρ P _ hP
  let R : Representation ℂ T P :=
    { toFun := fun t => (ρ t).restrict (hP t)
      map_one' := by
        ext y
        simp
      map_mul' := fun a b => by
        ext y
        simp }
  obtain ⟨E, h1, h2⟩ := exists_eigenchars (T := T) _ P R rfl
  refine ⟨E, fun t => ?_, fun μ => ?_⟩
  · rw [trIn, dite_eq_left (hP t)]
    exact h1 t
  · rw [h2]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨y, y.2, fun h0 => hy (Subtype.ext h0), fun t => congrArg Subtype.val (h t)⟩
    · rintro ⟨y, hyP, hy, h⟩
      exact ⟨⟨y, hyP⟩, fun h0 => hy (congrArg Subtype.val h0), fun t => Subtype.ext (h t)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuotAlt
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.traceQuot :
    UpperTheory.Gal.Join.TraceQuot := by
  intro V W _ _ _ _ S _ B p T hB hBT hnil
  have hTP : ∀ y ∈ Submodule.map p S, T y ∈ Submodule.map p S := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨B v, hB v, hBT v hv⟩
  have hBS : ∀ v ∈ S, B v ∈ S := fun v _ => hB v
  have hRS : LinearMap.range B ≤ S := by
    rintro _ ⟨v, rfl⟩
    exact hB v
  haveI : FiniteDimensional ℂ (LinearMap.range B) := Submodule.finiteDimensional_of_le hRS
  refine ⟨inferInstance, ?_⟩
  unfold trIn
  rw [dite_eq_left hTP]
  have h1 : LinearMap.trace ℂ (LinearMap.range B) (B.restrict (fun x _ => (⟨x, rfl⟩ : B x ∈ LinearMap.range B)))
      = LinearMap.trace ℂ S (B.restrict hBS) := by
    have key := LinearMap.trace_restrict_eq_of_forall_mem ((LinearMap.range B).comap S.subtype)
      (B.restrict hBS) (fun x => show B x ∈ LinearMap.range B from ⟨x, rfl⟩)
    rw [← key, ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hRS)]
    congr 1
  rw [h1]
  set q : S →ₗ[ℂ] Submodule.map p S := p.submoduleMap S with hqdef
  have hq : Function.Surjective q := p.submoduleMap_surjective S
  haveI : FiniteDimensional ℂ (Submodule.map p S) := Module.Finite.of_surjective q hq
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  set BS := B.restrict hBS with hBSdef
  set TP := T.restrict hTP with hTPdef
  have hint : q ∘ₗ BS = TP ∘ₗ q := by
    ext x
    exact hBT x.1 x.2
  have hT : TP = q ∘ₗ (BS ∘ₗ s) := by
    rw [← LinearMap.comp_assoc, hint, LinearMap.comp_assoc, hs, LinearMap.comp_id]
  rw [hT, LinearMap.trace_comp_comm']
  set E : S →ₗ[ℂ] S := LinearMap.id - s ∘ₗ q with hEdef
  have hsplit : BS = (BS ∘ₗ s) ∘ₗ q + BS ∘ₗ E := by
    ext x
    simp [hEdef]
  have hqs : ∀ y, q (s y) = y := fun y => LinearMap.congr_fun hs y
  have hqB : ∀ y : S, q y = 0 → q (BS y) = 0 := by
    intro y hy
    have := LinearMap.congr_fun hint y
    simp only [LinearMap.comp_apply] at this
    rw [this, hy, map_zero]
  have hzero : LinearMap.trace ℂ S (BS ∘ₗ E) = 0 := by
    rw [LinearMap.trace_comp_comm']
    have hK : ∀ x, (E ∘ₗ BS) x ∈ LinearMap.ker q := by
      intro x
      simp [hEdef, hqs]
    rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hK]
    set f := (E ∘ₗ BS).restrict (fun x _ => hK x) with hfdef
    apply IsNilpotent.eq_zero
    apply LinearMap.isNilpotent_trace_of_isNilpotent
    rw [Module.End.isNilpotent_iff_of_finite]
    intro k
    have hk0 : q k.1 = 0 := k.2
    have hpk : p k.1.1 = 0 := congrArg Subtype.val hk0
    obtain ⟨m, hm⟩ := hnil k.1.1 k.1.2 hpk
    refine ⟨m, ?_⟩
    have step : ∀ n : ℕ, ((f ^ n) k).1.1 = (B ^ n) k.1.1 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
        have hy : q ((f ^ n) k).1 = 0 := ((f ^ n) k).2
        show ((E (BS ((f ^ n) k).1)) : V) = B ((f ^ n) k).1.1
        rw [hEdef, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hqB _ hy, map_zero, sub_zero]
        rfl
    apply Subtype.ext
    apply Subtype.ext
    rw [step]
    simpa using hm
  conv_lhs => rw [hsplit]
  rw [map_add (f := _), hzero, add_zero]
end

