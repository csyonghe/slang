//TEST:SIMPLE(filecheck=CHECK): -target hlsl -entry computeMain -stage compute

// A conformance records DeadImplementation::evaluate in its witness table, but neither the table
// nor the method is reachable from computeMain. The specialization fixed point must not walk that
// witness edge: doing so would try to honor ForceUnroll with a runtime trip count and diagnose an
// error in code that the final module DCE removes.
interface IDead
{
    int evaluate(int count);
}

export struct DeadImplementation : IDead
{
    int evaluate(int count)
    {
        int result = 0;
        [ForceUnroll]
        for (int i = 0; i < count; ++i)
            result += i;
        return result;
    }
}

[numthreads(1, 1, 1)]
void computeMain()
{}

// CHECK: void computeMain()
