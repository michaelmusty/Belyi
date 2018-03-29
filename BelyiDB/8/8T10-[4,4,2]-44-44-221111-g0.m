s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T10-[4,4,2]-44-44-221111-g0";
s`BelyiDBFilename := "8T10-[4,4,2]-44-44-221111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 2 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 5, 2, 7, 4, 1, 6, 3, 8 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 16 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 4, 1, 6, 7, 8, 5, 2, 3 ],
[ 5, 2, 7, 4, 1, 6, 3, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 7, 4, 5, 2, 3, 8, 1, 6 ]:
 Order := 4 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 3, 8, 1, 6, 7, 4, 5, 2 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 1, 6, 7, 8, 5, 2, 3 ],
\[ 5, 2, 7, 4, 1, 6, 3, 8 ]:
 Order := 16 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 1, 6, 7, 8, 5, 2, 3 ],
\[ 5, 2, 7, 4, 1, 6, 3, 8 ]:
 Order := 16 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 1, 6, 7, 8, 5, 2, 3 ],
\[ 5, 2, 7, 4, 1, 6, 3, 8 ]:
 Order := 16 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 8, 5, 2, 3, 4, 1, 6, 7 ],
[ 1, 6, 3, 8, 5, 2, 7, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 2, 7, 4, 1, 6, 3, 8 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 16 >) |
[ PermutationGroup<8 |  
\[ 5, 2, 7, 4, 1, 6, 3, 8 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 16 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 4, 1, 6, 7, 8, 5, 2, 3 ],
[ 5, 2, 7, 4, 1, 6, 3, 8 ]
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
