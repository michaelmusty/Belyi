s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T38-[6,6,4]-611-62-422-g1";
s`BelyiDBFilename := "8T38-[6,6,4]-611-62-422-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 > |
[ 3, 1, 6, 4, 7, 5, 2, 8 ],
[ 8, 1, 7, 2, 4, 5, 3, 6 ],
[ 4, 3, 2, 5, 8, 7, 6, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 1, 6, 4, 7, 5, 2, 8 ],
\[ 8, 1, 7, 2, 4, 5, 3, 6 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ]:
 Order := 192 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 1, 6, 4, 7, 5, 2, 8 ],
\[ 8, 1, 7, 2, 4, 5, 3, 6 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 3, 1, 6, 4, 7, 5, 2, 8 ],
\[ 8, 1, 7, 2, 4, 5, 3, 6 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ]:
 Order := 192 > |
[ 3, 1, 6, 4, 7, 5, 2, 8 ],
[ 8, 1, 7, 2, 4, 5, 3, 6 ],
[ 4, 3, 2, 5, 8, 7, 6, 1 ]
],
[ PermutationGroup<8 |  
\[ 3, 1, 6, 4, 7, 5, 2, 8 ],
\[ 8, 1, 7, 2, 4, 5, 3, 6 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ]:
 Order := 192 > |
[ 3, 1, 6, 4, 7, 5, 2, 8 ],
[ 5, 4, 2, 7, 1, 8, 6, 3 ],
[ 3, 4, 5, 2, 7, 8, 1, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 > |
[ 3, 1, 6, 4, 7, 5, 2, 8 ],
[ 8, 1, 7, 2, 4, 5, 3, 6 ],
[ 4, 3, 2, 5, 8, 7, 6, 1 ]
],
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 > |
[ 4, 2, 1, 7, 8, 6, 5, 3 ],
[ 5, 8, 2, 3, 1, 4, 6, 7 ],
[ 4, 3, 2, 5, 8, 7, 6, 1 ]
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
