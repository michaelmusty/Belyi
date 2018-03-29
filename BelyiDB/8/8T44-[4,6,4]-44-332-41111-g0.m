s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T44-[4,6,4]-44-332-41111-g0";
s`BelyiDBFilename := "8T44-[4,6,4]-44-332-41111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 5, 8, 2, 7, 1, 4, 6, 3 ],
[ 2, 5, 3, 4, 6, 1, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 8, 2, 7, 1, 4, 6, 3 ],
\[ 2, 5, 3, 4, 6, 1, 7, 8 ]:
 Order := 384 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 8, 2, 7, 1, 4, 6, 3 ],
\[ 2, 5, 3, 4, 6, 1, 7, 8 ]:
 Order := 384 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 8, 2, 7, 1, 4, 6, 3 ],
\[ 2, 5, 3, 4, 6, 1, 7, 8 ]:
 Order := 384 > |
[ 8, 1, 2, 7, 4, 5, 6, 3 ],
[ 5, 3, 8, 6, 1, 7, 4, 2 ],
[ 8, 2, 3, 1, 4, 6, 7, 5 ]
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
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 5, 8, 2, 7, 1, 4, 6, 3 ],
[ 2, 5, 3, 4, 6, 1, 7, 8 ]
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
