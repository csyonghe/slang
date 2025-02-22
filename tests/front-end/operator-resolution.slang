
//TEST:SIMPLE(filecheck=CHECK):-target hlsl -entry computeMain -profile cs_6_0

RWStructuredBuffer<int> outputBuffer;

[numthreads(1,1,1)]
void computeMain()
{
    // CHECK: 4001
    int8_t a = 1;
    // we should resolve + to call +<int32_t> here.
    outputBuffer[0] = a + 4000;
}