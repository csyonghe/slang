//TEST:SIMPLE(filecheck=CHECK): -target cuda -entry tileMain -stage tile

// CHECK: __tile_global__ void tileMain
[shader("tile")]
void tileMain(uint3 gid : SV_GroupID)
{

}