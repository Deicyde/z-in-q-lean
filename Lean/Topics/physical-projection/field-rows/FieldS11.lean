import BucketCheck
namespace PhysicalProjection.FieldRows
open ZeroInput.Sparse ProjectionDescent Triangular.Data Sparse PhysicalProjection.Comparison
set_option maxRecDepth 20000
set_option maxHeartbeats 1800000
private def bin0_0 := ap (sp (164^2) small11) (sp (-1) (sp (-6724) RF.2))
private def bin1_0 := bin0_0.filter (bit 0)
private def bin1_1 := bin0_0.filter (fun t=> !bit 0 t)
private def bin2_0 := bin1_0.filter (bit 1)
private def bin2_1 := bin1_0.filter (fun t=> !bit 1 t)
private def bin2_2 := bin1_1.filter (bit 1)
private def bin2_3 := bin1_1.filter (fun t=> !bit 1 t)
private def bin3_0 := bin2_0.filter (bit 2)
private def bin3_1 := bin2_0.filter (fun t=> !bit 2 t)
private def bin3_2 := bin2_1.filter (bit 2)
private def bin3_3 := bin2_1.filter (fun t=> !bit 2 t)
private def bin3_4 := bin2_2.filter (bit 2)
private def bin3_5 := bin2_2.filter (fun t=> !bit 2 t)
private def bin3_6 := bin2_3.filter (bit 2)
private def bin3_7 := bin2_3.filter (fun t=> !bit 2 t)
private def bin4_0 := bin3_0.filter (bit 3)
private def bin4_1 := bin3_0.filter (fun t=> !bit 3 t)
private def bin4_2 := bin3_1.filter (bit 3)
private def bin4_3 := bin3_1.filter (fun t=> !bit 3 t)
private def bin4_4 := bin3_2.filter (bit 3)
private def bin4_5 := bin3_2.filter (fun t=> !bit 3 t)
private def bin4_6 := bin3_3.filter (bit 3)
private def bin4_7 := bin3_3.filter (fun t=> !bit 3 t)
private def bin4_8 := bin3_4.filter (bit 3)
private def bin4_9 := bin3_4.filter (fun t=> !bit 3 t)
private def bin4_10 := bin3_5.filter (bit 3)
private def bin4_11 := bin3_5.filter (fun t=> !bit 3 t)
private def bin4_12 := bin3_6.filter (bit 3)
private def bin4_13 := bin3_6.filter (fun t=> !bit 3 t)
private def bin4_14 := bin3_7.filter (bit 3)
private def bin4_15 := bin3_7.filter (fun t=> !bit 3 t)
private theorem yes4_0 : branches 4 bin4_0 0=true := by decide
private theorem yes4_1 : branches 4 bin4_1 0=true := by decide
private theorem yes4_2 : branches 4 bin4_2 0=true := by decide
private theorem yes4_3 : branches 4 bin4_3 0=true := by decide
private theorem yes4_4 : branches 4 bin4_4 0=true := by decide
private theorem yes4_5 : branches 4 bin4_5 0=true := by decide
private theorem yes4_6 : branches 4 bin4_6 0=true := by decide
private theorem yes4_7 : branches 4 bin4_7 0=true := by decide
private theorem yes4_8 : branches 4 bin4_8 0=true := by decide
private theorem yes4_9 : branches 4 bin4_9 0=true := by decide
private theorem yes4_10 : branches 4 bin4_10 0=true := by decide
private theorem yes4_11 : branches 4 bin4_11 0=true := by decide
private theorem yes4_12 : branches 4 bin4_12 0=true := by decide
private theorem yes4_13 : branches 4 bin4_13 0=true := by decide
private theorem yes4_14 : branches 4 bin4_14 0=true := by decide
private theorem yes4_15 : branches 4 bin4_15 0=true := by decide
private theorem yes3_0 : branches 3 bin3_0 1=true := by change (branches 4 bin4_0 0 && branches 4 bin4_1 0)=true;rw [yes4_0,yes4_1];rfl
private theorem yes3_1 : branches 3 bin3_1 1=true := by change (branches 4 bin4_2 0 && branches 4 bin4_3 0)=true;rw [yes4_2,yes4_3];rfl
private theorem yes3_2 : branches 3 bin3_2 1=true := by change (branches 4 bin4_4 0 && branches 4 bin4_5 0)=true;rw [yes4_4,yes4_5];rfl
private theorem yes3_3 : branches 3 bin3_3 1=true := by change (branches 4 bin4_6 0 && branches 4 bin4_7 0)=true;rw [yes4_6,yes4_7];rfl
private theorem yes3_4 : branches 3 bin3_4 1=true := by change (branches 4 bin4_8 0 && branches 4 bin4_9 0)=true;rw [yes4_8,yes4_9];rfl
private theorem yes3_5 : branches 3 bin3_5 1=true := by change (branches 4 bin4_10 0 && branches 4 bin4_11 0)=true;rw [yes4_10,yes4_11];rfl
private theorem yes3_6 : branches 3 bin3_6 1=true := by change (branches 4 bin4_12 0 && branches 4 bin4_13 0)=true;rw [yes4_12,yes4_13];rfl
private theorem yes3_7 : branches 3 bin3_7 1=true := by change (branches 4 bin4_14 0 && branches 4 bin4_15 0)=true;rw [yes4_14,yes4_15];rfl
private theorem yes2_0 : branches 2 bin2_0 2=true := by change (branches 3 bin3_0 1 && branches 3 bin3_1 1)=true;rw [yes3_0,yes3_1];rfl
private theorem yes2_1 : branches 2 bin2_1 2=true := by change (branches 3 bin3_2 1 && branches 3 bin3_3 1)=true;rw [yes3_2,yes3_3];rfl
private theorem yes2_2 : branches 2 bin2_2 2=true := by change (branches 3 bin3_4 1 && branches 3 bin3_5 1)=true;rw [yes3_4,yes3_5];rfl
private theorem yes2_3 : branches 2 bin2_3 2=true := by change (branches 3 bin3_6 1 && branches 3 bin3_7 1)=true;rw [yes3_6,yes3_7];rfl
private theorem yes1_0 : branches 1 bin1_0 3=true := by change (branches 2 bin2_0 2 && branches 2 bin2_1 2)=true;rw [yes2_0,yes2_1];rfl
private theorem yes1_1 : branches 1 bin1_1 3=true := by change (branches 2 bin2_2 2 && branches 2 bin2_3 2)=true;rw [yes2_2,yes2_3];rfl
private theorem exactData : branches 0 bin0_0 4=true := by change (branches 1 bin1_0 3 && branches 1 bin1_1 3)=true;rw [yes1_0,yes1_1];rfl

theorem literal11 (g : Bool) (z : Assignment) :
    value z (literal g .S .root true) = rowScale .S .root true * component true (formula g .S .root z) := by
  have matchAt (x : Assignment) : value x small11 = 3*(rowScale .S .root true * component true (plain g .S .root x)) := by
    have eq:=subtract_zero _ _ x (branches_zero 0 bin0_0 4 exactData x)
    rw [at_s,at_s] at eq
    have ind:=congrArg Prod.snd (r_sem x)
    change value x RF.2=((26896:Rat))*component true (plain false .S .root x) at ind
    rw [ind] at eq
    change value x small11=3*(rowScale .S .root true*component true (plain false .S .root x))
    simp only [rowScale] at *; grobner
  have phys:=congrArg (value z) data11
  rw [ProjectionDescent.scale_value,inflate_value,matchAt] at phys
  change value z p11=rowScale .S .root true * component true (plain g .S .root (shifted z))
  grobner
end PhysicalProjection.FieldRows
