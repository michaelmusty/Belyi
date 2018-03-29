s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T19-[4,4,2]-44-4211-2222-g0";
s`BelyiDBFilename := "8T19-[4,4,2]-44-4211-2222-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 2 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 32 > |
[ 6, 7, 4, 8, 3, 2, 1, 5 ],
[ 1, 8, 3, 5, 6, 7, 4, 2 ],
[ 6, 5, 4, 3, 2, 1, 8, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 3, 8, 1, 6, 7, 4, 5, 2 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 6, 7, 4, 8, 3, 2, 1, 5 ],
\[ 1, 8, 3, 5, 6, 7, 4, 2 ],
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 32 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 6, 7, 4, 8, 3, 2, 1, 5 ],
\[ 1, 8, 3, 5, 6, 7, 4, 2 ],
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 6, 7, 4, 8, 3, 2, 1, 5 ],
\[ 1, 8, 3, 5, 6, 7, 4, 2 ],
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 32 > |
[ 6, 7, 4, 8, 3, 2, 1, 5 ],
[ 8, 1, 2, 4, 7, 6, 5, 3 ],
[ 5, 6, 7, 8, 1, 2, 3, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 32 > |
[ 6, 7, 4, 8, 3, 2, 1, 5 ],
[ 1, 8, 3, 5, 6, 7, 4, 2 ],
[ 6, 5, 4, 3, 2, 1, 8, 7 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
