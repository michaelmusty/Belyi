s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T44-[4,6,2]-44-332-22211-g0";
s`BelyiDBFilename := "8T44-[4,6,2]-44-332-22211-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 6, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 > |
[ 2, 3, 4, 1, 6, 7, 8, 5 ],
[ 7, 5, 2, 8, 3, 1, 6, 4 ],
[ 8, 6, 3, 5, 4, 2, 7, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 7, 8, 5 ],
\[ 7, 5, 2, 8, 3, 1, 6, 4 ],
\[ 8, 6, 3, 5, 4, 2, 7, 1 ]:
 Order := 384 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 7, 8, 5 ],
\[ 7, 5, 2, 8, 3, 1, 6, 4 ],
\[ 8, 6, 3, 5, 4, 2, 7, 1 ]:
 Order := 384 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 7, 8, 5 ],
\[ 7, 5, 2, 8, 3, 1, 6, 4 ],
\[ 8, 6, 3, 5, 4, 2, 7, 1 ]:
 Order := 384 > |
[ 2, 3, 4, 1, 6, 7, 8, 5 ],
[ 7, 5, 2, 8, 3, 1, 6, 4 ],
[ 8, 6, 3, 5, 4, 2, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 7, 8, 5 ],
\[ 7, 5, 2, 8, 3, 1, 6, 4 ],
\[ 8, 6, 3, 5, 4, 2, 7, 1 ]:
 Order := 384 > |
[ 2, 3, 4, 1, 6, 7, 8, 5 ],
[ 4, 5, 7, 6, 8, 1, 3, 2 ],
[ 1, 6, 8, 7, 5, 2, 4, 3 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 >) |
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 > |
[ 2, 3, 4, 1, 6, 7, 8, 5 ],
[ 7, 5, 2, 8, 3, 1, 6, 4 ],
[ 8, 6, 3, 5, 4, 2, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 > |
[ 3, 4, 2, 1, 7, 8, 6, 5 ],
[ 6, 7, 1, 8, 2, 3, 5, 4 ],
[ 8, 6, 3, 5, 4, 2, 7, 1 ]
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
